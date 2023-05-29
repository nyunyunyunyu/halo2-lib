use crate::halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Assigned, Circuit, Column, ConstraintSystem, Error, Expression, Fixed},
    poly::Rotation,
};
use crate::util::expression::Expr;
pub use crate::util::H;
use crate::util::*;
use crate::util::{
    constraint_builder::BaseConstraintBuilder,
    expression::{select, xor},
};
use halo2_base::utils::ScalarField;
use log::{debug, info};
use std::{marker::PhantomData, vec};

/// Witness values per row.
#[derive(Clone, Debug, PartialEq)]
pub struct ShaRow<F> {
    w: [bool; NUM_BITS_PER_WORD_W],
    a: [bool; NUM_BITS_PER_WORD_EXT],
    e: [bool; NUM_BITS_PER_WORD_EXT],
    h_a_in: u32,
    h_e_in: u32,
    h_a_out: u32,
    h_e_out: u32,
    input_word: F,
}

/// Configuration for [`Sha256BitChip`].
#[derive(Clone, Debug)]
pub struct Sha256CompressionConfig<F> {
    q_enable: Column<Fixed>,
    q_extend: Column<Fixed>,
    q_start: Column<Fixed>,
    q_compression: Column<Fixed>,
    q_end: Column<Fixed>,
    q_padding: Column<Fixed>,
    q_squeeze: Column<Fixed>,
    round_cst: Column<Fixed>,
    word_w: [Column<Advice>; NUM_BITS_PER_WORD_W],
    word_a: [Column<Advice>; NUM_BITS_PER_WORD_EXT],
    word_e: [Column<Advice>; NUM_BITS_PER_WORD_EXT],
    /// Init hash values of a,b,c,d.
    pub h_a_in: Column<Advice>,
    /// Init hash values of e,f,g,h.
    pub h_e_in: Column<Advice>,
    /// Output hash values of a,b,c,d.
    pub h_a_out: Column<Advice>,
    /// Output hash values of e,f,g,h.
    pub h_e_out: Column<Advice>,
    /// The input words (4 bytes) result,
    pub input_words: Column<Advice>,
    _marker: PhantomData<F>,
}

/// Assigned values for each row.
#[derive(Clone, Debug)]
pub struct Sha256AssignedRows<'a, F: ScalarField> {
    /// Offset of the row.
    pub offset: usize,
    /// Input words at the row.
    pub input_words: Vec<AssignedCell<&'a Assigned<F>, F>>,
    /// Assigned h_a,h_b,h_c,h_d.
    pub h_a_in: Vec<AssignedCell<&'a Assigned<F>, F>>,
    /// Assigned h_e,h_f,h_g,h_h.
    pub h_e_in: Vec<AssignedCell<&'a Assigned<F>, F>>,
    /// Assigned h_a,h_b,h_c,h_d.
    pub h_a_out: Vec<AssignedCell<&'a Assigned<F>, F>>,
    /// Assigned h_e,h_f,h_g,h_h.
    pub h_e_out: Vec<AssignedCell<&'a Assigned<F>, F>>,
}

impl<'a, F: ScalarField> Sha256AssignedRows<'a, F> {
    const ROW_H_IN_PER_BLOCK: usize = 4;
    const ROW_H_OUT_PER_BLOCK: usize = 4;
    const ROW_INPUT_PER_BLOCK: usize = 16;
    /// Init [`Sha256AssignedRows`]
    pub fn new(offset: usize) -> Self {
        Self {
            offset,
            input_words: vec![],
            h_a_in: vec![],
            h_e_in: vec![],
            h_a_out: vec![],
            h_e_out: vec![],
        }
    }

    /// Get assigned input words.
    pub fn get_input_words(&self) -> Vec<Vec<AssignedCell<&Assigned<F>, F>>> {
        self.input_words.chunks(Self::ROW_INPUT_PER_BLOCK).map(|words| words.to_vec()).collect()
    }

    /// Get H_IN assigned values.
    pub fn get_h_ins(&self) -> Vec<Vec<AssignedCell<&Assigned<F>, F>>> {
        let mut assigned_h_ins = Vec::new();
        let num_block = self.h_a_in.len() / Self::ROW_H_IN_PER_BLOCK;
        for idx in 0..num_block {
            let h_a_in =
                &self.h_a_in[Self::ROW_H_IN_PER_BLOCK * idx..Self::ROW_H_IN_PER_BLOCK * (idx + 1)];
            let h_e_in =
                &self.h_e_in[Self::ROW_H_IN_PER_BLOCK * idx..Self::ROW_H_IN_PER_BLOCK * (idx + 1)];
            assigned_h_ins.push(vec![
                h_a_in[3].clone(),
                h_a_in[2].clone(),
                h_a_in[1].clone(),
                h_a_in[0].clone(),
                h_e_in[3].clone(),
                h_e_in[2].clone(),
                h_e_in[1].clone(),
                h_e_in[0].clone(),
            ]);
        }
        assigned_h_ins
    }

    /// Get H_OUR assigned values.
    pub fn get_h_outs(&self) -> Vec<Vec<AssignedCell<&Assigned<F>, F>>> {
        let mut assigned_h_outs = Vec::new();
        let num_block = self.h_a_out.len() / Self::ROW_H_OUT_PER_BLOCK;
        for idx in 0..num_block {
            let h_a_out = &self.h_a_out
                [Self::ROW_H_OUT_PER_BLOCK * idx..Self::ROW_H_OUT_PER_BLOCK * (idx + 1)];
            let h_e_out = &self.h_e_out
                [Self::ROW_H_OUT_PER_BLOCK * idx..Self::ROW_H_OUT_PER_BLOCK * (idx + 1)];
            assigned_h_outs.push(vec![
                h_a_out[3].clone(),
                h_a_out[2].clone(),
                h_a_out[1].clone(),
                h_a_out[0].clone(),
                h_e_out[3].clone(),
                h_e_out[2].clone(),
                h_e_out[1].clone(),
                h_e_out[0].clone(),
            ]);
        }
        assigned_h_outs
    }

    /// Append other assigned rows to myself.
    pub fn append(&mut self, other: &mut Self) {
        self.offset += other.offset;
        self.input_words.append(&mut other.input_words);
        // self.output_words.append(&mut other.output_words);
        self.h_a_in.append(&mut other.h_a_in);
        self.h_e_in.append(&mut other.h_e_in);
        self.h_a_out.append(&mut other.h_a_out);
        self.h_e_out.append(&mut other.h_e_out);
    }
}

impl<F: ScalarField> Sha256CompressionConfig<F> {
    /// The number of rows per 64 bytes input block.
    pub const ROWS_PER_BLOCK: usize = 72;
    /// Configure constraints for [`Sha256BitChip`]
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.fixed_column();
        let q_extend = meta.fixed_column();
        let q_start = meta.fixed_column();
        let q_compression = meta.fixed_column();
        let q_end = meta.fixed_column();
        let q_padding = meta.fixed_column();
        let q_squeeze = meta.fixed_column();
        let word_w = array_init::array_init(|_| meta.advice_column());
        let word_a = array_init::array_init(|_| meta.advice_column());
        let word_e = array_init::array_init(|_| meta.advice_column());
        let round_cst = meta.fixed_column();
        let h_a_in = meta.advice_column();
        meta.enable_equality(h_a_in);
        let h_e_in = meta.advice_column();
        meta.enable_equality(h_e_in);
        let h_a_out = meta.advice_column();
        meta.enable_equality(h_a_out);
        let h_e_out = meta.advice_column();
        meta.enable_equality(h_e_out);
        let input_words = meta.advice_column();
        meta.enable_equality(input_words);
        // State bits
        let mut w_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_W];
        let mut w_2 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_7 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_15 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_16 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut a = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut b = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut c = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut d = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut e = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut f = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut g = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut h = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut d_64 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut h_64 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut new_a_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_EXT];
        let mut new_e_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_EXT];
        meta.create_gate("Query state bits", |meta| {
            for k in 0..NUM_BITS_PER_WORD_W {
                w_ext[k] = meta.query_advice(word_w[k], Rotation(-0));
            }
            for i in 0..NUM_BITS_PER_WORD {
                let k = i + NUM_BITS_PER_WORD_W - NUM_BITS_PER_WORD;
                w_2[i] = meta.query_advice(word_w[k], Rotation(-2));
                w_7[i] = meta.query_advice(word_w[k], Rotation(-7));
                w_15[i] = meta.query_advice(word_w[k], Rotation(-15));
                w_16[i] = meta.query_advice(word_w[k], Rotation(-16));
                let k = i + NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD;
                a[i] = meta.query_advice(word_a[k], Rotation(-1));
                b[i] = meta.query_advice(word_a[k], Rotation(-2));
                c[i] = meta.query_advice(word_a[k], Rotation(-3));
                d[i] = meta.query_advice(word_a[k], Rotation(-4));
                e[i] = meta.query_advice(word_e[k], Rotation(-1));
                f[i] = meta.query_advice(word_e[k], Rotation(-2));
                g[i] = meta.query_advice(word_e[k], Rotation(-3));
                h[i] = meta.query_advice(word_e[k], Rotation(-4));
                d_64[i] = meta.query_advice(word_a[k], Rotation(-((NUM_ROUNDS + 4) as i32)));
                h_64[i] = meta.query_advice(word_e[k], Rotation(-((NUM_ROUNDS + 4) as i32)));
            }
            for k in 0..NUM_BITS_PER_WORD_EXT {
                new_a_ext[k] = meta.query_advice(word_a[k], Rotation(0));
                new_e_ext[k] = meta.query_advice(word_e[k], Rotation(0));
            }
            vec![0u64.expr()]
        });
        let w = &w_ext[NUM_BITS_PER_WORD_W - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_W];
        let new_a = &new_a_ext[NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_EXT];
        let new_e = &new_e_ext[NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_EXT];

        let xor = |a: &[Expression<F>], b: &[Expression<F>]| {
            debug_assert_eq!(a.len(), b.len(), "invalid length");
            let mut c = vec![0.expr(); a.len()];
            for (idx, (a, b)) in a.iter().zip(b.iter()).enumerate() {
                c[idx] = xor::expr(a, b);
            }
            c
        };

        let select =
            |c: &[Expression<F>], when_true: &[Expression<F>], when_false: &[Expression<F>]| {
                debug_assert_eq!(c.len(), when_true.len(), "invalid length");
                debug_assert_eq!(c.len(), when_false.len(), "invalid length");
                let mut r = vec![0.expr(); c.len()];
                for (idx, (c, (when_true, when_false))) in
                    c.iter().zip(when_true.iter().zip(when_false.iter())).enumerate()
                {
                    r[idx] = select::expr(c.clone(), when_true.clone(), when_false.clone());
                }
                r
            };

        meta.create_gate("input checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            for w in w_ext.iter() {
                cb.require_boolean("w bit boolean", w.clone());
            }
            for a in new_a_ext.iter() {
                cb.require_boolean("a bit boolean", a.clone());
            }
            for e in new_e_ext.iter() {
                cb.require_boolean("e bit boolean", e.clone());
            }
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("w extend", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let s0 = xor(
                &rotate::expr(&w_15, 7),
                &xor(&rotate::expr(&w_15, 18), &shift::expr(&w_15, 3)),
            );
            let s1 =
                xor(&rotate::expr(&w_2, 17), &xor(&rotate::expr(&w_2, 19), &shift::expr(&w_2, 10)));
            let new_w =
                decode::expr(&w_16) + decode::expr(&s0) + decode::expr(&w_7) + decode::expr(&s1);
            cb.require_equal("w", new_w, decode::expr(&w_ext));
            cb.gate(meta.query_fixed(q_extend, Rotation::cur()))
        });

        meta.create_gate("compression", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let s1 = xor(&rotate::expr(&e, 6), &xor(&rotate::expr(&e, 11), &rotate::expr(&e, 25)));
            let ch = select(&e, &f, &g);
            let temp1 = decode::expr(&h)
                + decode::expr(&s1)
                + decode::expr(&ch)
                + meta.query_fixed(round_cst, Rotation::cur())
                + decode::expr(w);

            let s0 = xor(&rotate::expr(&a, 2), &xor(&rotate::expr(&a, 13), &rotate::expr(&a, 22)));
            let maj = select(&xor(&b, &c), &a, &b);
            let temp2 = decode::expr(&s0) + decode::expr(&maj);
            cb.require_equal("compress a", decode::expr(&new_a_ext), temp1.clone() + temp2);
            cb.require_equal("compress e", decode::expr(&new_e_ext), decode::expr(&d) + temp1);
            cb.gate(meta.query_fixed(q_compression, Rotation::cur()))
        });

        meta.create_gate("start", |meta| {
            let h_a_in = meta.query_advice(h_a_in, Rotation::cur());
            let h_e_in = meta.query_advice(h_e_in, Rotation::cur());
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let new_a_ext = decode::expr(&new_a_ext);
            let new_e_ext = decode::expr(&new_e_ext);
            let q_start = meta.query_fixed(q_start, Rotation::cur());
            // let q_first = meta.query_fixed(q_first, Rotation::cur());
            cb.require_equal(
                "start a", new_a_ext,
                h_a_in, //select::expr(q_first.expr(), h_a_in.expr(), decode::expr(&d)),
            );
            cb.require_equal(
                "start e", new_e_ext,
                h_e_in, //select::expr(q_first.expr(), h_e_in.expr(), decode::expr(&h)),
            );
            cb.gate(q_start)
        });

        meta.create_gate("end", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_equal(
                "end a",
                decode::expr(&new_a_ext),
                decode::expr(&d) + decode::expr(&d_64),
            );
            cb.require_equal(
                "end e",
                decode::expr(&new_e_ext),
                decode::expr(&h) + decode::expr(&h_64),
            );
            cb.gate(meta.query_fixed(q_end, Rotation::cur()))
        });

        // Create bytes from input bits
        let input_bytes = to_le_bytes::expr(w);

        // Input bytes
        meta.create_gate("input bytes", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let input_words = meta.query_advice(input_words, Rotation::cur());
            let sum = input_bytes[0].clone()
                + (1u64 << 8).expr() * input_bytes[1].clone()
                + (1u64 << 16).expr() * input_bytes[2].clone()
                + (1u64 << 24).expr() * input_bytes[3].clone();
            cb.require_equal("input_bytes = input_words", sum, input_words);
            cb.gate(meta.query_fixed(q_padding, Rotation::cur()))
        });

        // Squeeze
        meta.create_gate("squeeze", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            // Squeeze out the hash
            let hash_parts = [new_a, &a, &b, &c, new_e, &e, &f, &g];
            let hash_bytes = hash_parts
                .into_iter()
                .flat_map(|bits| to_le_bytes::expr(bits))
                .collect::<Vec<Expression<F>>>();
            let hash_words = hash_bytes
                .chunks(4)
                .map(|vals| {
                    let mut sum = 0u64.expr();
                    for idx in 0..4 {
                        sum = sum + vals[idx].clone() * (1u64 << (24 - 8 * idx)).expr();
                    }
                    sum
                })
                .collect::<Vec<Expression<F>>>();
            // let r = meta.query_advice(randomness, Rotation::cur());
            // let rlc = compose_rlc::expr(&hash_bytes, r);
            let h_a_outs = (0..4)
                .map(|idx| meta.query_advice(h_a_out, Rotation(-idx)))
                .collect::<Vec<Expression<F>>>();
            let h_e_outs = (0..4)
                .map(|idx| meta.query_advice(h_e_out, Rotation(-idx)))
                .collect::<Vec<Expression<F>>>();
            for idx in 0..4 {
                cb.require_equal(
                    "equal ouputs of a,b,c,d",
                    h_a_outs[idx].expr(),
                    hash_words[idx].expr(),
                );
                cb.require_equal(
                    "equal ouputs of e,f,g,h",
                    h_e_outs[idx].expr(),
                    hash_words[4 + idx].expr(),
                );
            }
            cb.gate(meta.query_fixed(q_squeeze, Rotation::cur()))
        });

        info!("degree: {}", meta.degree());

        Self {
            q_enable,
            q_extend,
            q_start,
            q_compression,
            q_end,
            q_padding,
            q_squeeze,
            word_w,
            word_a,
            word_e,
            round_cst,
            h_a_in,
            h_e_in,
            h_a_out,
            h_e_out,
            input_words,
            _marker: PhantomData,
        }
    }

    /// Given the input, returns a vector of the assigned cells for the hash
    /// results.
    ///
    /// # Arguments
    /// * region - a region where the witnesses are assigned.
    /// * inputs - a vector of input bytes.
    ///
    /// # Return values
    /// Returns a vector of the assigned cells for the hash results.
    pub fn digest(
        &self,
        region: &mut Region<'_, F>,
        input: &[u8],
        hs: [u64; 8],
    ) -> Result<(Sha256AssignedRows<F>, [u64; 8]), Error> {
        let (witness, next_hs) = self.compute_witness(input, hs);
        let mut assigned_rows = Sha256AssignedRows::new(0);
        self.assign_witness(region, &witness, &mut assigned_rows)?;
        Ok((assigned_rows, next_hs))
    }
    /// Given the witness for each row, returns a vector of the assigned cells
    /// for the hash.
    pub fn assign_witness(
        &self,
        region: &mut Region<'_, F>,
        witness: &[ShaRow<F>],
        assigned_rows: &mut Sha256AssignedRows<F>,
    ) -> Result<(), Error> {
        // let mut assigned_rows = Sha256AssignedRows::new();
        for sha256_row in witness.iter() {
            self.set_row(region, sha256_row, assigned_rows)?
        }
        Ok(())
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        row: &ShaRow<F>,
        assigned_rows: &mut Sha256AssignedRows<F>,
    ) -> Result<(), Error> {
        let offset = assigned_rows.offset;
        assigned_rows.offset += 1;
        let round = offset % (NUM_ROUNDS + 8);
        // let cur_offset = offset - pre_sha2_row_numbers;
        // Fixed values
        for (_name, column, value) in &[
            ("q_enable", self.q_enable, F::from(true)),
            ("q_start", self.q_start, F::from(round < 4)),
            ("q_extend", self.q_extend, F::from((4 + 16..4 + NUM_ROUNDS).contains(&round))),
            ("q_compression", self.q_compression, F::from((4..NUM_ROUNDS + 4).contains(&round))),
            ("q_end", self.q_end, F::from(round >= NUM_ROUNDS + 4)),
            ("q_padding", self.q_padding, F::from((4..20).contains(&round))),
            ("q_squeeze", self.q_squeeze, F::from(round == NUM_ROUNDS + 7)),
            (
                "round_cst",
                self.round_cst,
                F::from(if (4..NUM_ROUNDS + 4).contains(&round) {
                    ROUND_CST[round - 4] as u64
                } else {
                    0
                }),
            ),
        ] {
            region.assign_fixed(*column, offset, value);
        }

        // Advice values
        for (_name, columns, values) in [
            ("w bits", self.word_w.as_slice(), row.w.as_slice()),
            ("a bits", self.word_a.as_slice(), row.a.as_slice()),
            ("e bits", self.word_e.as_slice(), row.e.as_slice()),
        ] {
            for (_idx, (value, column)) in values.iter().zip(columns.iter()).enumerate() {
                #[cfg(feature = "halo2-axiom")]
                region.assign_advice(*column, offset, Value::known(F::from(*value)));
                #[cfg(not(feature = "halo2-axiom"))]
                region.assign_advice(
                    || format!("assign {} {} {}", name, idx, offset),
                    *column,
                    offset,
                    || Value::known(F::from(*value)),
                )?;
            }
        }

        let h_a_in =
            region.assign_advice(self.h_a_in, offset, Value::known(F::from(row.h_a_in as u64)));
        let h_e_in =
            region.assign_advice(self.h_e_in, offset, Value::known(F::from(row.h_e_in as u64)));
        let h_a_out =
            region.assign_advice(self.h_a_out, offset, Value::known(F::from(row.h_a_out as u64)));
        let h_e_out =
            region.assign_advice(self.h_e_out, offset, Value::known(F::from(row.h_e_out as u64)));

        let input_word =
            region.assign_advice(self.input_words, offset, Value::known(row.input_word));

        if round < 4 {
            assigned_rows.h_a_in.push(h_a_in);
            assigned_rows.h_e_in.push(h_e_in);
        }

        if (4..20).contains(&round) {
            assigned_rows.input_words.push(input_word);
            // assigned_rows.is_dummy.push(is_dummy);
        }

        if round >= NUM_ROUNDS + 4 {
            assigned_rows.h_a_out.push(h_a_out);
            assigned_rows.h_e_out.push(h_e_out);
        }

        Ok(())
    }

    /// Compute the witness values.
    pub fn compute_witness(&self, input_bytes: &[u8], hs: [u64; 8]) -> (Vec<ShaRow<F>>, [u64; 8]) {
        let bits = into_bits(input_bytes);
        assert_eq!(bits.len(), 8 * 64);
        let mut rows = Vec::<ShaRow<F>>::new();
        let mut hs = hs;

        // Process a block.
        let mut add_row = |w: u64,
                           a: u64,
                           e: u64,
                           input_word,
                           h_a_in: u32,
                           h_e_in: u32,
                           h_a_out: u32,
                           h_e_out: u32| {
            let word_to_bits = |value: u64, num_bits: usize| {
                into_bits(&value.to_be_bytes())[64 - num_bits..64]
                    .iter()
                    .map(|b| *b != 0)
                    .into_iter()
                    .collect::<Vec<_>>()
            };
            rows.push(ShaRow {
                w: word_to_bits(w, NUM_BITS_PER_WORD_W).try_into().unwrap(),
                a: word_to_bits(a, NUM_BITS_PER_WORD_EXT).try_into().unwrap(),
                e: word_to_bits(e, NUM_BITS_PER_WORD_EXT).try_into().unwrap(),
                input_word,
                h_a_in,
                h_e_in,
                h_a_out,
                h_e_out,
            });
        };

        // Set the state
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) =
            (hs[0], hs[1], hs[2], hs[3], hs[4], hs[5], hs[6], hs[7]);

        let mut add_row_start =
            |a: u64, e: u64| add_row(0, a, e, F::zero(), a as u32, e as u32, 0, 0);
        add_row_start(d, h);
        add_row_start(c, g);
        add_row_start(b, f);
        add_row_start(a, e);

        let mut ws = Vec::new();
        for (round, round_cst) in ROUND_CST.iter().enumerate() {
            // w
            let w_ext = if round < NUM_WORDS_TO_ABSORB {
                decode::value(&bits[round * 32..(round + 1) * 32])
            } else {
                let get_w = |offset: usize| ws[ws.len() - offset] & 0xFFFFFFFF;
                let s0 = rotate::value(get_w(15), 7)
                    ^ rotate::value(get_w(15), 18)
                    ^ shift::value(get_w(15), 3);
                let s1 = rotate::value(get_w(2), 17)
                    ^ rotate::value(get_w(2), 19)
                    ^ shift::value(get_w(2), 10);
                get_w(16) + s0 + get_w(7) + s1
            };
            let input_word = if round < NUM_WORDS_TO_ABSORB {
                let bytes = to_le_bytes::value(&bits[round * 32..(round + 1) * 32]);
                let sum: u64 = (bytes[0] as u64)
                    + (1u64 << 8) * (bytes[1] as u64)
                    + (1u64 << 16) * (bytes[2] as u64)
                    + (1u64 << 24) * (bytes[3] as u64);
                F::from(sum)
            } else {
                F::zero()
            };
            let w = w_ext & 0xFFFFFFFF;
            ws.push(w);

            // compression
            let s1 = rotate::value(e, 6) ^ rotate::value(e, 11) ^ rotate::value(e, 25);
            let ch = (e & f) ^ (!e & g);
            let temp1 = h + s1 + ch + (*round_cst as u64) + w;
            let s0 = rotate::value(a, 2) ^ rotate::value(a, 13) ^ rotate::value(a, 22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0 + maj;

            h = g;
            g = f;
            f = e;
            e = d + temp1;
            d = c;
            c = b;
            b = a;
            a = temp1 + temp2;

            // Add the row
            add_row(w_ext, a, e, input_word, 0, 0, 0, 0);

            // Truncate the newly calculated values
            a &= 0xFFFFFFFF;
            e &= 0xFFFFFFFF;
        }

        // Accumulate
        hs[0] += a;
        hs[1] += b;
        hs[2] += c;
        hs[3] += d;
        hs[4] += e;
        hs[5] += f;
        hs[6] += g;
        hs[7] += h;

        let hash_words = {
            let hash_bytes = hs.iter().flat_map(|h| (*h as u32).to_be_bytes()).collect::<Vec<_>>();
            hash_bytes
                .chunks(8)
                .map(|vals| {
                    let mut sum = 0u64;
                    for idx in 0..8 {
                        sum = sum + (vals[idx] as u64) * (1u64 << (8 * idx));
                    }
                    sum
                })
                .collect::<Vec<u64>>()
        };
        if cfg!(debug_assertions) {
            dbg!("hash words {:x?}", hash_words.clone());
        }

        // Add end rows
        let mut add_row_end =
            |a: u64, e: u64| add_row(0, a, e, F::zero(), 0, 0, a as u32, e as u32);
        add_row_end(hs[3], hs[7]);
        add_row_end(hs[2], hs[6]);
        add_row_end(hs[1], hs[5]);
        add_row_end(hs[0], hs[4]);

        // Now truncate the results
        for h in hs.iter_mut() {
            *h &= 0xFFFFFFFF;
        }

        (rows, hs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    #[derive(Debug, Clone)]
    struct TestSha256Config<F: ScalarField> {
        sha256_config: Sha256CompressionConfig<F>,
    }

    #[derive(Default, Debug, Clone)]
    struct TestSha256<F: ScalarField> {
        input: Vec<u8>,
        _f: PhantomData<F>,
    }

    impl<F: ScalarField> Circuit<F> for TestSha256<F> {
        type Config = TestSha256Config<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let sha256_config = Sha256CompressionConfig::configure(meta);
            Self::Config { sha256_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // let sha256chip =
            //     Sha256CompressionConfig::new(config.sha256_config.clone(),
            // self.max_input_len);
            let init_hs = H;
            layouter.assign_region(
                || "digest",
                |mut region| config.sha256_config.digest(&mut region, &self.input[0..64], init_hs),
            )?;
            //layouter.constrain_instance(first_r.cell(), config.instance, 0)?;
            Ok(())
        }
    }

    fn verify<F: ScalarField>(k: u32, input: Vec<u8>, success: bool) {
        let circuit = TestSha256 { input, _f: PhantomData };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let verify_result = prover.verify();
        if verify_result.is_ok() != success {
            if let Some(errors) = verify_result.err() {
                for error in errors.iter() {
                    println!("{}", error);
                }
            }
            panic!();
        }
    }

    #[test]
    fn bit_sha256_simple1() {
        let k = 8;
        let inputs = (0u8..64).collect::<Vec<_>>();
        verify::<Fr>(k, inputs, true);
    }

    // #[test]
    // fn bit_sha256_simple2() {
    //     let k = 11;
    //     let inputs = vec![1u8; 1000];
    //     verify::<Fr>(k, inputs, 1024, true);
    // }

    // #[test]
    // fn bit_sha256_simple3() {
    //     let k = 11;
    //     let inputs = vec![0u8];
    //     verify::<Fr>(k, inputs, 128, true);
    // }

    #[derive(Debug, Clone)]
    struct TestSha256DoubleConfig<F: ScalarField> {
        sha256_configs: [Sha256CompressionConfig<F>; 2],
    }

    #[derive(Debug, Clone)]
    enum Sha256Strategy {
        Vertical,
        Horizontal,
    }

    #[derive(Debug, Clone)]
    struct TestSha256Double<F: ScalarField> {
        input: Vec<u8>,
        strategy: Sha256Strategy,
        _f: PhantomData<F>,
    }

    impl<F: ScalarField> Circuit<F> for TestSha256Double<F> {
        type Config = TestSha256DoubleConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let sha256_config1 = Sha256CompressionConfig::configure(meta);
            let sha256_config2 = Sha256CompressionConfig::configure(meta);
            Self::Config { sha256_configs: [sha256_config1, sha256_config2] }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // assert!(self.max_input_len % 2 == 0);
            // let sha256chip1 =
            //     Sha256BitChip::new(config.sha256_configs[0].clone(), self.max_input_len /
            // 2); let sha256chip2 =
            //     Sha256BitChip::new(config.sha256_configs[1].clone(), self.max_input_len /
            // 2);
            let init_hs = H;
            let (witness0, next_hs) = config.sha256_configs[0]
                .compute_witness(&self.input[0..self.input.len() / 2], init_hs);
            let (witness1, _) = config.sha256_configs[1]
                .compute_witness(&self.input[self.input.len() / 2..self.input.len()], next_hs);

            layouter.assign_region(
                || "digest double",
                |mut region| {
                    // sha256chip1.digest(&mut region, &self.input[0..self.input.len() / 2]);
                    let mut assigned_rows1 = Sha256AssignedRows::<F>::new(0);
                    config.sha256_configs[0].assign_witness(
                        &mut region,
                        &witness0,
                        &mut assigned_rows1,
                    )?;
                    let mut assigned_rows2 = match self.strategy {
                        Sha256Strategy::Vertical => {
                            Sha256AssignedRows::new(Sha256CompressionConfig::<F>::ROWS_PER_BLOCK)
                        }
                        Sha256Strategy::Horizontal => Sha256AssignedRows::new(0),
                    };
                    let next_config = match self.strategy {
                        Sha256Strategy::Vertical => &config.sha256_configs[0],
                        Sha256Strategy::Horizontal => &config.sha256_configs[1],
                    };
                    next_config.assign_witness(&mut region, &witness1, &mut assigned_rows2)?;
                    let h_outs = assigned_rows1.get_h_outs();
                    assert_eq!(h_outs.len(), 1);
                    let h_ins = assigned_rows2.get_h_ins();
                    assert_eq!(h_ins.len(), 1);
                    for (h_in, h_out) in h_ins[0].iter().zip(h_outs[0].iter()) {
                        region.constrain_equal(h_in.cell(), h_out.cell());
                    }
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    fn verify_double<F: ScalarField>(
        k: u32,
        input: Vec<u8>,
        strategy: Sha256Strategy,
        success: bool,
    ) {
        let circuit = TestSha256Double { input, strategy, _f: PhantomData };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let verify_result = prover.verify();
        if verify_result.is_ok() != success {
            if let Some(errors) = verify_result.err() {
                for error in errors.iter() {
                    println!("{}", error);
                }
            }
            panic!();
        }
    }

    #[test]
    fn bit_sha256_double_vertical() {
        let k = 11;
        let inputs = vec![0u8; 128];
        verify_double::<Fr>(k, inputs, Sha256Strategy::Vertical, true);
    }

    #[test]
    fn bit_sha256_double_horizontal() {
        let k = 11;
        let inputs = vec![0u8; 128];
        verify_double::<Fr>(k, inputs, Sha256Strategy::Horizontal, true);
    }
}
