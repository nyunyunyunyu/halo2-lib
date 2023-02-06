use serde::{Deserialize, Serialize};

use super::{
    AssignedValue, Context,
    QuantumCell::{self, Constant, Existing, Witness, WitnessFraction},
};
use crate::utils::ScalarField;
use crate::{
    halo2_proofs::{
        plonk::{
            Advice, Assigned, Column, ConstraintSystem, FirstPhase, Fixed, SecondPhase, Selector,
            ThirdPhase,
        },
        poly::Rotation,
    },
    ContextCell,
};
use std::{
    iter::{self},
    marker::PhantomData,
};

/// The maximum number of phases halo2 currently supports
pub const MAX_PHASE: usize = 3;

// Currently there is only one strategy, but we may add more in the future
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub enum GateStrategy {
    Vertical,
}

#[derive(Clone, Debug)]
pub struct BasicGateConfig<F: ScalarField> {
    // `q_enable` will have either length 1 or 2, depending on the strategy

    // If strategy is Vertical, then this is the basic vertical gate
    // `q_0 * (a + b * c - d) = 0`
    // where
    // * a = value[0], b = value[1], c = value[2], d = value[3]
    // * q = q_enable[0]
    // * q_i is either 0 or 1 so this is just a simple selector
    // We chose `a + b * c` instead of `a * b + c` to allow "chaining" of gates, i.e., the output of one gate because `a` in the next gate
    pub q_enable: Selector,
    // one column to store the inputs and outputs of the gate
    pub value: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: ScalarField> BasicGateConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, strategy: GateStrategy, phase: u8) -> Self {
        let value = match phase {
            0 => meta.advice_column_in(FirstPhase),
            1 => meta.advice_column_in(SecondPhase),
            2 => meta.advice_column_in(ThirdPhase),
            _ => panic!("Currently BasicGate only supports {MAX_PHASE} phases"),
        };
        meta.enable_equality(value);

        let q_enable = meta.selector();

        match strategy {
            GateStrategy::Vertical => {
                let config = Self { q_enable, value, _marker: PhantomData };
                config.create_gate(meta);
                config
            }
        }
    }

    fn create_gate(&self, meta: &mut ConstraintSystem<F>) {
        meta.create_gate("1 column a * b + c = out", |meta| {
            let q = meta.query_selector(self.q_enable);

            let a = meta.query_advice(self.value, Rotation::cur());
            let b = meta.query_advice(self.value, Rotation::next());
            let c = meta.query_advice(self.value, Rotation(2));
            let out = meta.query_advice(self.value, Rotation(3));

            vec![q * (a + b * c - out)]
        })
    }
}

#[derive(Clone, Debug)]
pub struct FlexGateConfig<F: ScalarField> {
    pub basic_gates: [Vec<BasicGateConfig<F>>; MAX_PHASE],
    // `constants` is a vector of fixed columns for allocating constant values
    pub constants: Vec<Column<Fixed>>,
    pub num_advice: [usize; MAX_PHASE],
    _strategy: GateStrategy,
    pub max_rows: usize,
}

impl<F: ScalarField> FlexGateConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        strategy: GateStrategy,
        num_advice: &[usize],
        num_fixed: usize,
        // log2_ceil(# rows in circuit)
        circuit_degree: usize,
    ) -> Self {
        let mut constants = Vec::with_capacity(num_fixed);
        for _i in 0..num_fixed {
            let c = meta.fixed_column();
            meta.enable_equality(c);
            // meta.enable_constant(c);
            constants.push(c);
        }

        match strategy {
            GateStrategy::Vertical => {
                let mut basic_gates = [(); MAX_PHASE].map(|_| vec![]);
                let mut num_advice_array = [0usize; MAX_PHASE];
                for ((phase, &num_columns), gates) in
                    num_advice.iter().enumerate().zip(basic_gates.iter_mut())
                {
                    *gates = (0..num_columns)
                        .map(|_| BasicGateConfig::configure(meta, strategy, phase as u8))
                        .collect();
                    num_advice_array[phase] = num_columns;
                }
                Self {
                    basic_gates,
                    constants,
                    num_advice: num_advice_array,
                    _strategy: strategy,
                    /// Warning: this needs to be updated if you create more advice columns after this `FlexGateConfig` is created
                    max_rows: (1 << circuit_degree) - meta.minimum_rows(),
                }
            }
        }
    }
}

pub trait GateInstructions<F: ScalarField> {
    fn strategy(&self) -> GateStrategy;

    fn pow_of_two(&self) -> &[F];
    fn get_field_element(&self, n: u64) -> F;

    /// Copies a, b and constrains `a + b * 1 = out`
    // | a | b | 1 | a + b |
    fn add(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let out_val = *a.value() + b.value();
        ctx.assign_region_last(vec![a, b, Constant(F::one()), Witness(out_val)], vec![0])
    }

    /// Copies a, b and constrains `a + b * (-1) = out`
    // | a - b | b | 1 | a |
    fn sub(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let out_val = *a.value() - b.value();
        // slightly better to not have to compute -F::one() since F::one() is cached
        ctx.assign_region(vec![Witness(out_val), b, Constant(F::one()), a], vec![0]);
        ctx.get(-4)
    }

    // | a | -a | 1 | 0 |
    fn neg(&self, ctx: &mut Context<F>, a: impl Into<QuantumCell<F>>) -> AssignedValue<F> {
        let a = a.into();
        let out_val = -*a.value();
        ctx.assign_region(
            vec![a, Witness(out_val), Constant(F::one()), Constant(F::zero())],
            vec![0],
        );
        ctx.get(-3)
    }

    /// Copies a, b and constrains `0 + a * b = out`
    // | 0 | a | b | a * b |
    fn mul(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let out_val = *a.value() * b.value();
        ctx.assign_region_last(vec![Constant(F::zero()), a, b, Witness(out_val)], vec![0])
    }

    /// a * b + c
    fn mul_add(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
        c: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let c = c.into();
        let out_val = *a.value() * b.value() + c.value();
        ctx.assign_region_last(vec![c, a, b, Witness(out_val)], vec![0])
    }

    /// (1 - a) * b = b - a * b
    fn mul_not(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let out_val = (F::one() - a.value()) * b.value();
        ctx.assign_region_smart(vec![Witness(out_val), a, b, b], vec![0], vec![(2, 3)], []);
        ctx.get(-4)
    }

    /// Constrain x is 0 or 1.
    fn assert_bit(&self, ctx: &mut Context<F>, x: AssignedValue<F>) {
        ctx.assign_region(
            vec![Constant(F::zero()), Existing(x), Existing(x), Existing(x)],
            vec![0],
        );
    }

    fn div_unsafe(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        // TODO: if really necessary, make `c` of type `Assigned<F>`
        // this would require the API using `Assigned<F>` instead of `F` everywhere, so leave as last resort
        let c = b.value().invert().unwrap() * a.value();
        ctx.assign_region(vec![Constant(F::zero()), Witness(c), b, a], vec![0]);
        ctx.get(-3)
    }

    fn assert_is_const(&self, ctx: &mut Context<F>, a: &AssignedValue<F>, constant: &F) {
        if !ctx.witness_gen_only {
            let c_index = ctx.assign_fixed(*constant);
            ctx.constant_equality_constraints.push((
                ContextCell { context_id: ctx.context_id, offset: c_index },
                a.cell.unwrap(),
            ));
        }
    }

    /// Returns the inner product of `<a, b>`
    fn inner_product<QA>(
        &self,
        ctx: &mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QuantumCell<F>>,
    ) -> AssignedValue<F>
    where
        QA: Into<QuantumCell<F>>;

    /// Returns the inner product of `<a, b>` and the last item of `a` after it is assigned
    fn inner_product_left_last<QA>(
        &self,
        ctx: &mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QuantumCell<F>>,
    ) -> (AssignedValue<F>, AssignedValue<F>)
    where
        QA: Into<QuantumCell<F>>;

    /// Returns a vector with the partial sums `sum_{j=0..=i} a[j] * b[j]`.
    fn inner_product_with_sums<'thread, QA>(
        &self,
        ctx: &'thread mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QuantumCell<F>>,
    ) -> Box<dyn Iterator<Item = AssignedValue<F>> + 'thread>
    where
        QA: Into<QuantumCell<F>>;

    fn sum<Q>(&self, ctx: &mut Context<F>, a: impl IntoIterator<Item = Q>) -> AssignedValue<F>
    where
        Q: Into<QuantumCell<F>>,
    {
        let mut a = a.into_iter().peekable();
        let start = a.next();
        if start.is_none() {
            return ctx.load_zero();
        }
        let start = start.unwrap().into();
        if a.peek().is_none() {
            return ctx.assign_region_last([start], []);
        }
        let (len, hi) = a.size_hint();
        debug_assert_eq!(Some(len), hi);

        let mut sum = *start.value();
        let cells = iter::once(start).chain(a.flat_map(|a| {
            let a = a.into();
            sum += a.value();
            [a, Constant(F::one()), Witness(sum)]
        }));
        ctx.assign_region_last(cells, (0..len).map(|i| 3 * i as isize))
    }

    /// Returns the assignment trace where `output[i]` has the running sum `sum_{j=0..=i} a[j]`
    fn partial_sums<'thread, Q>(
        &self,
        ctx: &'thread mut Context<F>,
        a: impl IntoIterator<Item = Q>,
    ) -> Box<dyn Iterator<Item = AssignedValue<F>> + 'thread>
    where
        Q: Into<QuantumCell<F>>,
    {
        let mut a = a.into_iter().peekable();
        let start = a.next();
        if start.is_none() {
            return Box::new(iter::once(ctx.load_zero()));
        }
        let start = start.unwrap().into();
        if a.peek().is_none() {
            return Box::new(iter::once(ctx.assign_region_last([start], [])));
        }
        let (len, hi) = a.size_hint();
        debug_assert_eq!(Some(len), hi);

        let mut sum = *start.value();
        let cells = iter::once(start).chain(a.flat_map(|a| {
            let a = a.into();
            sum += a.value();
            [a, Constant(F::one()), Witness(sum)]
        }));
        ctx.assign_region(cells, (0..len).map(|i| 3 * i as isize));
        Box::new((0..=len).rev().map(|i| ctx.get(-1 - 3 * (i as isize))))
    }

    // requires b.len() == a.len() + 1
    // returns
    // x_i = b_1 * (a_1...a_{i - 1})
    //     + b_2 * (a_2...a_{i - 1})
    //     + ...
    //     + b_i
    // Returns [x_1, ..., x_{b.len()}]
    fn accumulated_product<QA, QB>(
        &self,
        ctx: &mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QB>,
    ) -> Vec<AssignedValue<F>>
    where
        QA: Into<QuantumCell<F>>,
        QB: Into<QuantumCell<F>>,
    {
        let mut b = b.into_iter();
        let mut a = a.into_iter();
        let b_first = b.next();
        if let Some(b_first) = b_first {
            let b_first = ctx.assign_region_last([b_first], []);
            std::iter::successors(Some(b_first), |x| {
                a.next().zip(b.next()).map(|(a, b)| self.mul_add(ctx, Existing(*x), a, b))
            })
            .collect()
        } else {
            vec![]
        }
    }

    fn sum_products_with_coeff_and_var(
        &self,
        ctx: &mut Context<F>,
        values: impl IntoIterator<Item = (F, QuantumCell<F>, QuantumCell<F>)>,
        var: QuantumCell<F>,
    ) -> AssignedValue<F>;

    // | 1 - b | 1 | b | 1 | b | a | 1 - b | out |
    fn or(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let not_b_val = F::one() - b.value();
        let out_val = *a.value() + b.value() - *a.value() * b.value();
        let cells = vec![
            Witness(not_b_val),
            Constant(F::one()),
            b,
            Constant(F::one()),
            b,
            a,
            Witness(not_b_val),
            Witness(out_val),
        ];
        ctx.assign_region_smart(cells, vec![0, 4], vec![(0, 6), (2, 4)], vec![]);
        ctx.last().unwrap()
    }

    // | 0 | a | b | out |
    fn and(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        self.mul(ctx, a, b)
    }

    fn not(&self, ctx: &mut Context<F>, a: impl Into<QuantumCell<F>>) -> AssignedValue<F> {
        self.sub(ctx, Constant(F::one()), a)
    }

    /// assumes sel is boolean
    /// returns
    ///   a * sel + b * (1 - sel)
    fn select(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
        sel: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F>;

    /// returns: a || (b && c)
    // | 1 - b c | b | c | 1 | a - 1 | 1 - b c | out | a - 1 | 1 | 1 | a |
    fn or_and(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
        c: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F>;

    /// assume bits has boolean values
    /// returns vec[idx] with vec[idx] = 1 if and only if bits == idx as a binary number
    fn bits_to_indicator(
        &self,
        ctx: &mut Context<F>,
        bits: &[AssignedValue<F>],
    ) -> Vec<AssignedValue<F>> {
        let k = bits.len();

        let (inv_last_bit, last_bit) = {
            ctx.assign_region(
                vec![
                    Witness(F::one() - bits[k - 1].value()),
                    Existing(bits[k - 1]),
                    Constant(F::one()),
                    Constant(F::one()),
                ],
                vec![0],
            );
            (ctx.get(-4), ctx.get(-3))
        };
        let mut indicator = Vec::with_capacity(2 * (1 << k) - 2);
        let mut offset = 0;
        indicator.push(inv_last_bit);
        indicator.push(last_bit);
        for (idx, bit) in bits.iter().rev().enumerate().skip(1) {
            for old_idx in 0..(1 << idx) {
                let inv_prod_val = (F::one() - bit.value()) * indicator[offset + old_idx].value();
                ctx.assign_region(
                    vec![
                        Witness(inv_prod_val),
                        Existing(indicator[offset + old_idx]),
                        Existing(*bit),
                        Existing(indicator[offset + old_idx]),
                    ],
                    vec![0],
                );
                indicator.push(ctx.get(-4));

                let prod = self.mul(ctx, Existing(indicator[offset + old_idx]), Existing(*bit));
                indicator.push(prod);
            }
            offset += 1 << idx;
        }
        indicator.split_off((1 << k) - 2)
    }

    // returns vec with vec.len() == len such that:
    //     vec[i] == 1{i == idx}
    fn idx_to_indicator(
        &self,
        ctx: &mut Context<F>,
        idx: impl Into<QuantumCell<F>>,
        len: usize,
    ) -> Vec<AssignedValue<F>> {
        let mut idx = idx.into();
        let mut ind = Vec::with_capacity(len);
        let idx_val = idx.value().get_lower_32() as usize;
        for i in 0..len {
            // check ind[i] * (i - idx) == 0
            let ind_val = F::from(idx_val == i);
            let val = if idx_val == i { *idx.value() } else { F::zero() };
            ctx.assign_region_smart(
                vec![
                    Constant(F::zero()),
                    Witness(ind_val),
                    idx,
                    Witness(val),
                    Constant(-F::from(i as u64)),
                    Witness(ind_val),
                    Constant(F::zero()),
                ],
                vec![0, 3],
                vec![(1, 5)],
                vec![],
            );
            ind.push(ctx.get(-2));
            // need to use assigned idx after i > 0 so equality constraint holds
            if i == 0 {
                idx = Existing(ctx.get(-5));
            }
        }
        ind
    }

    // performs inner product on a, indicator
    // `indicator` values are all boolean
    /// Assumes for witness generation that only one element of `indicator` has non-zero value and that value is `F::one()`.
    fn select_by_indicator<Q>(
        &self,
        ctx: &mut Context<F>,
        a: impl IntoIterator<Item = Q>,
        indicator: impl IntoIterator<Item = AssignedValue<F>>,
    ) -> AssignedValue<F>
    where
        Q: Into<QuantumCell<F>>,
    {
        let mut sum = F::zero();
        let a = a.into_iter();
        let (len, hi) = a.size_hint();
        debug_assert_eq!(Some(len), hi);

        let cells = std::iter::once(Constant(F::zero())).chain(
            a.zip(indicator.into_iter()).flat_map(|(a, ind)| {
                let a = a.into();
                sum = if ind.value().is_zero_vartime() { sum } else { *a.value() };
                [a, Existing(ind), Witness(sum)]
            }),
        );
        ctx.assign_region_last(cells, (0..len).map(|i| 3 * i as isize))
    }

    fn select_from_idx<Q>(
        &self,
        ctx: &mut Context<F>,
        cells: impl IntoIterator<Item = Q>,
        idx: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F>
    where
        Q: Into<QuantumCell<F>>,
    {
        let cells = cells.into_iter();
        let (len, hi) = cells.size_hint();
        debug_assert_eq!(Some(len), hi);

        let ind = self.idx_to_indicator(ctx, idx, len);
        self.select_by_indicator(ctx, cells, ind)
    }

    // | out | a | inv | 1 | 0 | a | out | 0
    fn is_zero(&self, ctx: &mut Context<F>, a: AssignedValue<F>) -> AssignedValue<F> {
        let x = a.value();
        let (is_zero, inv) = if x.is_zero_vartime() {
            (F::one(), Assigned::Trivial(F::one()))
        } else {
            (F::zero(), Assigned::Rational(F::one(), *x))
        };

        let cells = vec![
            Witness(is_zero),
            Existing(a),
            WitnessFraction(inv),
            Constant(F::one()),
            Constant(F::zero()),
            Existing(a),
            Witness(is_zero),
            Constant(F::zero()),
        ];
        ctx.assign_region_smart(cells, vec![0, 4], vec![(0, 6)], []);
        ctx.get(-2)
    }

    fn is_equal(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let diff = self.sub(ctx, a, b);
        self.is_zero(ctx, diff)
    }

    /// returns little-endian bit vectors
    fn num_to_bits(
        &self,
        ctx: &mut Context<F>,
        a: AssignedValue<F>,
        range_bits: usize,
    ) -> Vec<AssignedValue<F>>;

    /// given pairs `coords[i] = (x_i, y_i)`, let `f` be the unique degree `len(coords)` polynomial such that `f(x_i) = y_i` for all `i`.
    ///
    /// input: coords, x
    ///
    /// output: (f(x), Prod_i (x - x_i))
    ///
    /// constrains all x_i and x are distinct
    fn lagrange_and_eval(
        &self,
        ctx: &mut Context<F>,
        coords: &[(AssignedValue<F>, AssignedValue<F>)],
        x: AssignedValue<F>,
    ) -> (AssignedValue<F>, AssignedValue<F>) {
        let mut z = self.sub(ctx, Existing(x), Existing(coords[0].0));
        for coord in coords.iter().skip(1) {
            let sub = self.sub(ctx, Existing(x), Existing(coord.0));
            z = self.mul(ctx, Existing(z), Existing(sub));
        }
        let mut eval = None;
        for i in 0..coords.len() {
            // compute (x - x_i) * Prod_{j != i} (x_i - x_j)
            let mut denom = self.sub(ctx, Existing(x), Existing(coords[i].0));
            for j in 0..coords.len() {
                if i == j {
                    continue;
                }
                let sub = self.sub(ctx, coords[i].0, coords[j].0);
                denom = self.mul(ctx, denom, sub);
            }
            // TODO: batch inversion
            let is_zero = self.is_zero(ctx, denom);
            self.assert_is_const(ctx, &is_zero, &F::zero());

            // y_i / denom
            let quot = self.div_unsafe(ctx, coords[i].1, denom);
            eval = if let Some(eval) = eval {
                let eval = self.add(ctx, eval, quot);
                Some(eval)
            } else {
                Some(quot)
            };
        }
        let out = self.mul(ctx, eval.unwrap(), z);
        (out, z)
    }
}

#[derive(Clone, Debug)]
pub struct GateChip<F: ScalarField> {
    strategy: GateStrategy,
    pub pow_of_two: Vec<F>,
    /// To avoid Montgomery conversion in `F::from` for common small numbers, we keep a cache of field elements
    pub field_element_cache: Vec<F>,
}

impl<F: ScalarField> Default for GateChip<F> {
    fn default() -> Self {
        Self::new(GateStrategy::Vertical)
    }
}

impl<F: ScalarField> GateChip<F> {
    pub fn new(strategy: GateStrategy) -> Self {
        let mut pow_of_two = Vec::with_capacity(F::NUM_BITS as usize);
        let two = F::from(2);
        pow_of_two.push(F::one());
        pow_of_two.push(two);
        for _ in 2..F::NUM_BITS {
            pow_of_two.push(two * pow_of_two.last().unwrap());
        }
        let field_element_cache = (0..1024).map(|i| F::from(i)).collect();

        Self { strategy, pow_of_two, field_element_cache }
    }

    fn inner_product_simple<QA>(
        &self,
        ctx: &mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QuantumCell<F>>,
    ) -> bool
    where
        QA: Into<QuantumCell<F>>,
    {
        let mut sum;
        let mut a = a.into_iter();
        let mut b = b.into_iter().peekable();

        let b_starts_with_one = matches!(b.peek(), Some(Constant(c)) if c == &F::one());
        let cells = if b_starts_with_one {
            b.next();
            let start_a = a.next().unwrap().into();
            sum = *start_a.value();
            iter::once(start_a)
        } else {
            sum = F::zero();
            iter::once(Constant(F::zero()))
        }
        .chain(a.zip(b).flat_map(|(a, b)| {
            let a = a.into();
            sum += *a.value() * b.value();
            [a, b, Witness(sum)]
        }));

        let gate_offsets = if ctx.witness_gen_only() {
            vec![]
        } else {
            let (lo, hi) = cells.size_hint();
            debug_assert_eq!(Some(lo), hi);
            let len = lo / 3;
            (0..len).map(|i| 3 * i as isize).collect()
        };
        ctx.assign_region(cells, gate_offsets);
        b_starts_with_one
    }
}

impl<F: ScalarField> GateInstructions<F> for GateChip<F> {
    fn strategy(&self) -> GateStrategy {
        self.strategy
    }
    fn pow_of_two(&self) -> &[F] {
        &self.pow_of_two
    }
    fn get_field_element(&self, n: u64) -> F {
        let get = self.field_element_cache.get(n as usize);
        if let Some(fe) = get {
            *fe
        } else {
            F::from(n)
        }
    }

    fn inner_product<QA>(
        &self,
        ctx: &mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QuantumCell<F>>,
    ) -> AssignedValue<F>
    where
        QA: Into<QuantumCell<F>>,
    {
        self.inner_product_simple(ctx, a, b);
        ctx.last().unwrap()
    }

    /// Returns the inner product of `<a, b>` and the last item of `a` after it is assigned
    fn inner_product_left_last<QA>(
        &self,
        ctx: &mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QuantumCell<F>>,
    ) -> (AssignedValue<F>, AssignedValue<F>)
    where
        QA: Into<QuantumCell<F>>,
    {
        let a = a.into_iter();
        let (len, hi) = a.size_hint();
        debug_assert_eq!(Some(len), hi);
        let row_offset = ctx.advice.len();
        let b_starts_with_one = self.inner_product_simple(ctx, a, b);
        let a_last = if b_starts_with_one {
            if len == 1 {
                ctx.get(row_offset as isize)
            } else {
                ctx.get((row_offset + 1 + 3 * (len - 2)) as isize)
            }
        } else {
            ctx.get((row_offset + 1 + 3 * (len - 1)) as isize)
        };
        (ctx.last().unwrap(), a_last)
    }

    /// Returns a vector with the partial sums `sum_{j=0..=i} a[j] * b[j]`.
    fn inner_product_with_sums<'thread, QA>(
        &self,
        ctx: &'thread mut Context<F>,
        a: impl IntoIterator<Item = QA>,
        b: impl IntoIterator<Item = QuantumCell<F>>,
    ) -> Box<dyn Iterator<Item = AssignedValue<F>> + 'thread>
    where
        QA: Into<QuantumCell<F>>,
    {
        let row_offset = ctx.advice.len();
        let b_starts_with_one = self.inner_product_simple(ctx, a, b);
        if b_starts_with_one {
            Box::new((row_offset..ctx.advice.len()).step_by(3).map(|i| ctx.get(i as isize)))
        } else {
            // in this case the first assignment is 0 so we skip it
            Box::new((row_offset..ctx.advice.len()).step_by(3).skip(1).map(|i| ctx.get(i as isize)))
        }
    }

    fn sum_products_with_coeff_and_var(
        &self,
        ctx: &mut Context<F>,
        values: impl IntoIterator<Item = (F, QuantumCell<F>, QuantumCell<F>)>,
        var: QuantumCell<F>,
    ) -> AssignedValue<F> {
        // TODO: optimize
        match self.strategy {
            GateStrategy::Vertical => {
                let (a, b): (Vec<_>, Vec<_>) = std::iter::once((var, Constant(F::one())))
                    .chain(values.into_iter().filter_map(|(c, va, vb)| {
                        if c == F::one() {
                            Some((va, vb))
                        } else if c != F::zero() {
                            let prod = self.mul(ctx, va, vb);
                            Some((QuantumCell::Existing(prod), Constant(c)))
                        } else {
                            None
                        }
                    }))
                    .unzip();
                self.inner_product(ctx, a, b)
            }
        }
    }

    fn select(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
        sel: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let sel = sel.into();
        let diff_val = *a.value() - b.value();
        let out_val = diff_val * sel.value() + b.value();
        match self.strategy {
            // | a - b | 1 | b | a |
            // | b | sel | a - b | out |
            GateStrategy::Vertical => {
                let cells = vec![
                    Witness(diff_val),
                    Constant(F::one()),
                    b,
                    a,
                    b,
                    sel,
                    Witness(diff_val),
                    Witness(out_val),
                ];
                ctx.assign_region_smart(cells, vec![0, 4], vec![(0, 6), (2, 4)], []);
                ctx.last().unwrap()
            }
        }
    }

    /// returns: a || (b && c)
    // | 1 - b c | b | c | 1 | a - 1 | 1 - b c | out | a - 1 | 1 | 1 | a |
    fn or_and(
        &self,
        ctx: &mut Context<F>,
        a: impl Into<QuantumCell<F>>,
        b: impl Into<QuantumCell<F>>,
        c: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F> {
        let a = a.into();
        let b = b.into();
        let c = c.into();
        let bc_val = *b.value() * c.value();
        let not_bc_val = F::one() - bc_val;
        let not_a_val = *a.value() - F::one();
        let out_val = bc_val + a.value() - bc_val * a.value();
        let cells = vec![
            Witness(not_bc_val),
            b,
            c,
            Constant(F::one()),
            Witness(not_a_val),
            Witness(not_bc_val),
            Witness(out_val),
            Witness(not_a_val),
            Constant(F::one()),
            Constant(F::one()),
            a,
        ];
        ctx.assign_region_smart(cells, vec![0, 3, 7], vec![(4, 7), (0, 5)], []);
        ctx.get(-5)
    }

    // returns little-endian bit vectors
    fn num_to_bits(
        &self,
        ctx: &mut Context<F>,
        a: AssignedValue<F>,
        range_bits: usize,
    ) -> Vec<AssignedValue<F>> {
        let a_bytes = a.value().to_repr();
        let bits = a_bytes
            .as_ref()
            .iter()
            .flat_map(|byte| (0..8).map(|i| (*byte as u64 >> i) & 1))
            .take(range_bits)
            .map(|x| F::from(x));

        let mut bit_cells = Vec::with_capacity(range_bits);
        let row_offset = ctx.advice.len();
        let acc = self.inner_product(
            ctx,
            bits.map(Witness),
            self.pow_of_two[..range_bits].iter().map(|c| Constant(*c)),
        );
        ctx.constrain_equal(&a, &acc);
        debug_assert!(range_bits > 0);
        bit_cells.push(ctx.get(row_offset as isize));
        for i in 1..range_bits {
            bit_cells.push(ctx.get((row_offset + 1 + 3 * (i - 2)) as isize));
        }

        for bit_cell in &bit_cells {
            self.assert_bit(ctx, *bit_cell);
        }
        bit_cells
    }
}