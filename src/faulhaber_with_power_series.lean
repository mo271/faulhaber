import tactic
import tactic.gptf
import data.nat.prime
import data.nat.parity
import algebra.divisibility
import algebra.big_operators
import data.set.finite
import number_theory.bernoulli
import data.finset
import data.finset.basic
import data.nat.basic
import data.finset.nat_antidiagonal

import ring_theory.power_series.basic

open power_series


lemma power_series_addition (ha hb: ℕ → ℚ):
power_series.mk(ha) + power_series.mk(hb) =
power_series.mk(λ z, (ha z) + (hb z)) :=
begin
  ext,
  simp [coeff_mk],
end

lemma power_series_subtraction (ha hb: ℕ → ℚ):
power_series.mk(ha) - power_series.mk(hb) =
power_series.mk(λ z, (ha z) - (hb z)) :=
begin
  ext,
  simp [coeff_mk],
end

theorem expand_tonelli (n:ℕ):
(finset.range n).sum(λ k, power_series.mk (λ n, (k:ℚ)^n / n.factorial)) =
power_series.mk (λ p, (finset.range n).sum(λ k, k^p)/p.factorial) :=
begin
  induction n with n h,
  { simp, refl },
  rw [finset.sum_range_succ],
  rw [h],
  simp [power_series_addition],
  ext,
  simp only [coeff_mk, dif_pos, eq_self_iff_true, ne.def],
  rw [finset.sum_range_succ],
  rw [add_div],
end

lemma power_series_finset {n p : ℕ} (f: (ℕ → power_series ℚ)):
(coeff ℚ p)((finset.range n).sum (λ (k : ℕ), f k))  =
(finset.range n).sum (λ (k : ℕ),(coeff ℚ p) (f k)) :=
begin
  simp [coeff_mk],
end

def expk (k:ℕ) : power_series ℚ := power_series.mk (λ n, (k:ℚ)^n / n.factorial)

lemma expkrw (k:ℕ ): (expk k) = power_series.mk (λ n, (k:ℚ)^n / n.factorial) :=
begin
  refl,
end

lemma expk' (k:ℕ): (exp ℚ)^k = expk k :=
begin
  induction k with k h,
  rw [expk],
  ext,
  simp only [coeff_mk, coeff_one, nat.nat_zero_eq_zero, nat.factorial,
  nat.cast_zero, pow_zero],
  split_ifs,
  { simp [h] },
  { simp [h] },
  simp only [pow_succ, h],
  ext,
  rw [coeff_mul],
  simp [expk, exp],
  have hf: (n.factorial:ℚ) ≠ 0 :=
  begin
    simp only [n.factorial_ne_zero, ne.def, nat.cast_eq_zero, not_false_iff],
  end,
  rw [mul_mul_div ((finset.nat.antidiagonal n).sum
  (λ (x : ℕ × ℕ), (↑(x.fst.factorial))⁻¹ *
  (↑k ^ x.snd / ↑(x.snd.factorial)))) hf],
  rw [←div_eq_mul_one_div],
  rw [div_left_inj' hf],
  simp only,
  let  f: ℕ →  ℕ → ℚ := λ a:ℕ, λ b: ℕ,
  ((↑(a.factorial))⁻¹ * (↑k ^ b / ↑(b.factorial))),
  simp only [finset.nat.sum_antidiagonal_eq_sum_range_succ f],
  have hfab: ∀ (a b:ℕ), f a b =
  ((↑(a.factorial))⁻¹ * (↑k ^ b / ↑(b.factorial))) :=
  begin
    intros,
    refl,
  end,
  rw [add_comm ↑k],
  rw [add_pow],
  rw [finset.sum_mul],
  have hsucc: n.succ = n + 1 := by refl,
  simp only [←hsucc],
  refine finset.sum_congr rfl _,
  intro m,
  intro hm,
  rw [hfab],
  rw [finset.mem_range] at hm,
  have hnmn: n - m ≤ n :=
  begin
    apply nat.sub_le_left_of_le_add,
    apply nat.le_add_left,
  end,
  have hnm: m ≤ n :=
  begin
    exact nat.le_of_lt_succ hm,
  end,
  rw [←nat.choose_symm hnm],
  rw [nat.choose_eq_factorial_div_factorial hnmn],
  have hnnm: n - (n - m) = m :=
  begin
    exact nat.sub_sub_self hnm,
  end,
  rw [hnnm],
  simp only [one_pow, one_mul],
  rw [mul_comm  ((m.factorial):ℚ)⁻¹],
  simp only [nat.factorial_mul_factorial_dvd_factorial hnm],
  rw ← division_def,
  rw div_div_eq_div_mul,
  rw mul_comm,
  have hfacprod:  ↑(m.factorial * (n - m).factorial) ≠  0 :=
  begin
    have hmfacnezero: m.factorial ≠ 0:= ne_of_gt m.factorial_pos,
    have hnmfacnezero: (n-m).factorial ≠ 0 :=
    begin
      have hk: ∃ k, k = n - m:=
      begin
        simp only [exists_apply_eq_apply],
      end,
      refine ne_of_gt _,
      cases hk with k hk,
      have hkfac: k.factorial >0 :=  k.factorial_pos,
      rw hk at hkfac,
      exact hkfac,
    end,
    have hnn: m.factorial * (n - m).factorial ≠ 0 := mul_ne_zero hmfacnezero hnmfacnezero,
    simp [hnn],
  end,
  rw nat.cast_dvd,
  rw nat.cast_mul,
  simp only [← mul_div_assoc, mul_comm],
  rw mul_comm,
  exact nat.factorial_mul_factorial_dvd_factorial hnm,
  simp [hfacprod],
  simp [nat.factorial_ne_zero],
end

lemma expk_minus_one_coeff (n m:ℕ): (coeff ℚ m) ((expk n) - 1) =
( if (m > 0) then ((coeff ℚ m) (expk n)) else (((coeff ℚ 0) (expk n) - 1) ) ):=
begin
  split_ifs with h h,
  simp,
  have hnm: ¬(m = 0) := by apply ne_of_gt h,
  simp [hnm],
  simp,
  have hm: m = 0 := by linarith,
  rw [hm],
  simp,
end

lemma minus_one_minus_expk (n:ℕ): (1 - expk n) = - ((expk n) - 1) := by ring

theorem sum_geo_seq (n:ℕ) (φ : (power_series ℚ)):
((finset.range n).sum(λ k, φ^k) * (φ - 1)) = ((φ^n) - 1) :=
begin
  induction n with n h,
  simp,
  rw [finset.sum_range_succ],
  rw [pow_succ'],
  rw [add_mul],
  rw [h],
  ring,
end


theorem special_sum_inf_geo_seq (n:ℕ):
 (exp ℚ - 1) * (finset.range n).sum(λ k, expk k) = ((expk n) - 1) :=
begin
  have hone: ((finset.range n).sum(λ k, (exp ℚ)^k) * ((exp ℚ) - 1)) =
  (((exp ℚ)^n) - 1) := sum_geo_seq n ((exp ℚ)),
  simp only [expk', mul_comm] at *,
  exact hone,
end


theorem expand_fraction (n:ℕ):
(1 - expk n) * X * (exp ℚ - 1)  = (1 - exp ℚ) * (expk n - 1) * X :=
begin
  ring,
end


theorem right_series (n:ℕ):
(expk n - 1) = X*power_series.mk (λ p, n^p.succ/(p.succ.factorial)) :=
begin
  ext,
  rw [power_series.coeff_mul],
  rw [expk_minus_one_coeff],
  split_ifs with h_ge_zero h_zero,
  rw [expk],
  rw [power_series.coeff_mk],
  simp [power_series.coeff_X],
  have hnsucc: ∃ (m:ℕ), m.succ = n_1 :=
  begin
    use n_1 - 1,
    exact nat.succ_pred_eq_of_pos h_ge_zero,
  end,
  cases hnsucc with m hm,
  rw [←hm],
  rw [finset.nat.sum_antidiagonal_succ],
  simp,
  by_cases hmz: m = 0,
  rw [hmz],
  rw [finset.nat.antidiagonal_zero],
  simp,
  have hmsucc: ∃ (p:ℕ), p.succ = m :=
  begin
    have h_ge_zero: m > 0 :=
    begin
      exact nat.pos_of_ne_zero hmz,
    end,
    use m - 1,
    exact nat.succ_pred_eq_of_pos h_ge_zero,
  end,
  cases hmsucc with p hp,
  rw [←hp],
  rw [finset.nat.sum_antidiagonal_succ],
  by_cases hpz: p = 0,
  rw [hpz],
  simp,
  simp,
  have hn_1: n_1 = 0 := by linarith,
  rw [expk],
  simp only [hn_1],
  rw [power_series.coeff_mk],
  simp,
end



lemma minus_X_fw (φ ψ: power_series ℚ):
(φ = ψ) →  (
  mk(λ n, (-1)^n*(coeff ℚ n) φ) =
  mk(λ n, (-1)^n*(coeff ℚ n) ψ)) :=
begin
  rintro rfl,
  refl,
end

lemma minus_X (φ ψ: power_series ℚ):
(φ = ψ) ↔  (
  mk(λ n, (-1:ℚ)^n*(coeff ℚ n) φ) =
  mk(λ n, (-1)^n*(coeff ℚ n) ψ)) :=
begin
  split,
  exact minus_X_fw φ ψ,
  intro h,
  have g: mk(λ n,
  (-1:ℚ)^n*(coeff ℚ n) (mk(λ n, (-1)^n*(coeff ℚ n) φ))) =
  mk(λ n,
  (-1)^n*(coeff ℚ n) (mk(λ n, (-1)^n*(coeff ℚ n) ψ))) := (minus_X_fw (mk(λ n, (-1)^n*(coeff ℚ n) φ))
  (mk(λ n, (-1)^n*(coeff ℚ n) ψ))) h,
  simp at g,
  simp only [power_series.ext_iff] at g,
  simp at g,
  have hpn: ∀ n:ℕ, ((-1:ℚ)^n) ≠ 0 :=
  begin
    intro n,
    apply pow_ne_zero,
    rw [ne.def, neg_eq_zero],
    exact one_ne_zero,
  end,
  simp [hpn] at g,
  exact power_series.ext_iff.mpr g,
 end

 lemma minus_X_mul (φ ψ: power_series ℚ):
 (mk(λ n, (-1:ℚ)^n*(coeff ℚ n) φ) * mk(λ n, (-1:ℚ)^n*(coeff ℚ n) ψ)) =
 mk(λ n, (-1:ℚ)^n*(coeff ℚ n) (φ*ψ)) :=
 (ring_hom.map_mul (rescale (-1 : ℚ)) φ ψ).symm

lemma exp_inv:  (exp ℚ) * mk (λ (n : ℕ), (-1) ^ n * (coeff ℚ n) (exp ℚ))  = 1 :=
begin
  ext,
  rw [coeff_mul],
  simp only [one_div, coeff_mk, coeff_one, nat.factorial,
  coeff_exp, ring_hom.id_apply, rat.algebra_map_rat_rat],
  have zero_pow_ite_fac: 0^n/((n.factorial:ℚ)) =(ite(n=0) (1:ℚ) 0):=
  begin
    induction n with n hn,
    simp only [mul_one, nat.factorial_zero, if_true, eq_self_iff_true,
    nat.factorial_one, nat.cast_one, pow_zero],
    simp only [div_one],
    have hnsucc_zero: ¬ n.succ = 0 := nat.succ_ne_zero n,
    simp only [hnsucc_zero, if_false],
    have hsuccfac: n.succ.factorial ≠  0 := ne_of_gt (nat.factorial_pos _),
    simp only [nat.succ_pos', div_eq_zero_iff, true_or, zero_pow_eq_zero],
  end,
  rw [←zero_pow_ite_fac],
  have one_minus_one_eq_zero: 1 + (-1) = (0:ℚ) :=
  begin
    simp only [add_right_neg],
  end,
  rw [←one_minus_one_eq_zero],
  rw [add_pow],
  let f:ℕ → ℕ → ℚ := λ a : ℕ, λ b : ℕ,
  (((a.factorial))⁻¹ * ((-1) ^ b * ((b.factorial))⁻¹)),
  rw [finset.nat.sum_antidiagonal_eq_sum_range_succ f],
  have hfacnezero: (n.factorial:ℚ)  ≠ 0 := by exact_mod_cast n.factorial_ne_zero,
  symmetry,
  rw [div_eq_iff hfacnezero],
  rw [finset.sum_mul],
  have hsucc: n.succ = n + 1 := by refl,
  simp only [←hsucc],
  refine finset.sum_congr rfl _,
  intro m,
  intro hm,
  simp only [f],
  have hmn: m ≤ n :=
  begin
     rw [finset.mem_range] at hm,
     exact nat.le_of_lt_succ hm,
  end,
  simp only [nat.choose_eq_factorial_div_factorial hmn],
  simp only [one_pow, one_mul],
  rw ← mul_assoc,
  simp only,
  ring,
  simp only [mul_eq_mul_right_iff],
  left,
  have hfacprod:  ↑(m.factorial * (n - m).factorial) ≠  0 :=
  begin
    have hmfacnezero: m.factorial ≠ 0:= ne_of_gt m.factorial_pos,
    have hnmfacnezero: (n-m).factorial ≠ 0 :=
    begin
      have hk: ∃ k, k = n - m:=
      begin
        simp only [exists_apply_eq_apply],
      end,
      refine ne_of_gt _,
      cases hk with k hk,
      have hkfac: k.factorial >0 :=  k.factorial_pos,
      rw hk at hkfac,
      exact hkfac,
    end,
    have hnn: m.factorial * (n - m).factorial ≠ 0 := mul_ne_zero hmfacnezero hnmfacnezero,
    simp [hnn],
  end,
  rw nat.cast_dvd,
  simp,
  rw ←division_def,
  rw ←division_def,
  rw div_div_eq_div_mul,
  simp [mul_comm],
  exact nat.factorial_mul_factorial_dvd_factorial hmn,
  simp [hfacprod],
  simp [nat.factorial_ne_zero],
end

lemma expmxm1: mk (λ (n : ℕ), (-1:ℚ) ^ n * (coeff ℚ n) (exp ℚ - 1)) =
 (1 - exp ℚ)* mk (λ (n : ℕ), (-1) ^ n * (coeff ℚ n) (exp ℚ)) :=
 begin
   simp only [sub_mul, exp_inv],
   ext,
   simp only [one_div, coeff_mk, coeff_one, one_mul, coeff_exp,
   ring_hom.id_apply, linear_map.map_sub, rat.algebra_map_rat_rat],
   cases n,
   simp only [mul_one, nat.factorial_zero, if_true, eq_self_iff_true,
   nat.factorial_one, inv_one, nat.cast_one, mul_zero, pow_zero, sub_self],
   simp only [n.succ_ne_zero, sub_zero, if_false],
 end

variables {R : Type*} [ring R]

@[simp] lemma neg_one_pow_succ_succ {m : ℕ} : (-1 : R)^m.succ.succ = (-1)^m :=
begin
  change _ ^ (m + 2) = _,
  simp [pow_add],
end

@[simp] lemma neg_one_pow_succ_of_odd {m : ℕ}: (-1 : R) ^ (m + 1) = -(-1)^m :=
by simp [pow_add]

/--
lemma aux_exp2: mk (λ (n : ℕ), (-1:ℚ) ^ n * (coeff ℚ n) (X * exp ℚ)) =
(-X)*mk (λ (n : ℕ), (-1) ^ n * (coeff ℚ n) (exp ℚ)) :=
begin
  ext n,
  cases n,
  { simp only [←neg_mul_eq_neg_mul],
  simp only [mul_comm X (mk (λ (n : ℕ), (-1) ^ n * (coeff ℚ n) (exp ℚ))) ],
  simp only [neg_mul_eq_neg_mul],
  simp only [coeff_zero_mul_X],
  simp only [coeff_mk, linear_map.map_neg, mul_zero, neg_zero] },
  rw [mul_comm X, ←neg_mul_eq_neg_mul, mul_comm X, linear_map.map_neg],
  simp only [coeff_succ_mul_X, neg_mul_eq_neg_mul_symm, neg_one_pow_succ_of_odd, coeff_mk],
end
-/

lemma aux_exp2: mk (λ (n : ℕ), (-1:ℚ) ^ n * (coeff ℚ n) (X * exp ℚ)) =
(-X)*mk (λ (n : ℕ), (-1) ^ n * (coeff ℚ n) (exp ℚ)) :=
begin
  ext,
  simp only [coeff_mul, coeff_X, neg_mul_eq_neg_mul_symm, one_div, coeff_mk, linear_map.map_neg, nat.factorial, coeff_exp,
  boole_mul, ring_hom.id_apply, rat.algebra_map_rat_rat],
  cases n with p,
  { simp only [if_false, finset.nat.antidiagonal_zero, finset.sum_singleton, zero_ne_one, mul_zero, neg_zero]},
  simp only [finset.nat.sum_antidiagonal_succ, add_left_eq_self, nat.factorial, nat.cast_succ, nat.factorial_succ, if_false,
  zero_add, nat.cast_mul, zero_ne_one],
  cases p with m,
  { simp only [mul_one, nat.factorial_zero, if_true, eq_self_iff_true, nat.factorial_one, pow_one, finset.nat.antidiagonal_zero,
  inv_one, nat.cast_one, finset.sum_singleton, pow_zero]},
  simp only [finset.nat.sum_antidiagonal_succ, add_zero, if_true, eq_self_iff_true, nat.cast_succ, nat.factorial_succ,
  add_eq_zero_iff, if_false, one_ne_zero, finset.sum_const_zero, nat.cast_mul, and_false],
  simp [neg_one_pow_succ_succ],
end

theorem bernoulli_power_series':
  (exp ℚ - 1) * power_series.mk (λ n,
  ((-1)^n * bernoulli n / nat.factorial n : ℚ)) = X :=
begin
  have h: power_series.mk (λ n, (bernoulli n / nat.factorial n : ℚ)) * (exp ℚ - 1)
  = X * exp ℚ :=
  begin
    simp [bernoulli_power_series],
  end,
  rw minus_X at h,
  rw ←minus_X_mul at h,
  rw [expmxm1] at h,
  rw [aux_exp2] at h,
  let f1 := mk (λ (n : ℕ), (-1:ℚ) ^ n * (coeff ℚ n) (mk (λ (n : ℕ), bernoulli n / ↑(n.factorial)))),
  let f2 := 1 - exp ℚ,
  have hf2 : f2 = 1 - exp ℚ := by refl,
  let f3 := mk (λ (n : ℕ), (-1) ^ n * (coeff ℚ n) (exp ℚ)),
  rw [←(mul_assoc f1 f2 f3)] at h,
  have hf3: f3 = mk (λ (n : ℕ), (-1) ^ n * (coeff ℚ n) (exp ℚ)) := by refl,
  rw [←hf3] at h,
  have hf3_nonzero: f3 ≠ 0 :=
  begin
    rw [hf3],
    simp [power_series.ext_iff],
    use 1,
    simp,
  end,
  have g: f1*f2 = -X :=
  begin
    apply mul_right_cancel' hf3_nonzero h,
  end,
  have hf1: f1 = mk (λ (n : ℕ), (-1:ℚ) ^ n * (coeff ℚ n) (mk (λ (n : ℕ), bernoulli n / ↑(n.factorial)))) := by refl,
  simp at hf1,
  have hf1': f1 = mk (λ (n : ℕ), (-1) ^ n * bernoulli n / ↑(n.factorial)) :=
  begin
    simp [hf1],
    simp [power_series.ext_iff],
    intro n,
    rw [mul_div_assoc],
  end,
  rw [←hf1'],
  have hf2':  - f2 = (exp ℚ - 1) :=
  begin
    rw [hf2],
    ring,
  end,
  rw [←hf2'],
  rw [←neg_one_mul],
  rw [mul_assoc],
  rw [mul_comm f2],
  rw [g],
  simp,
end


-- this is missing in mathlib?!
theorem power_series_mul_assoc (φ₁ φ₂ φ₃ : (power_series ℚ)) :
φ₁ * (φ₂ * φ₃) = φ₁ * φ₂ * φ₃ :=
begin
  rw mv_power_series.mul_assoc, --  I'm sure its somewhere
end


theorem cauchy_prod (n:ℕ):
power_series.mk (λ n,
  ((-1)^n* bernoulli n / nat.factorial n : ℚ))*
  power_series.mk (λ p, (n:ℚ)^p.succ/(p.succ.factorial))  =
 power_series.mk (λp,
 ((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1))))) :=
begin
  ext q,
  rw [power_series.coeff_mul],
  simp [power_series.coeff_mk],
  let f: ℕ →  ℕ → ℚ := λ (a : ℕ), λ (b: ℕ),
  (-1) ^ a * bernoulli a / ↑(a.factorial) *
    (↑n ^ b.succ / ((↑(b) + 1) * ↑(b.factorial))),
  rw [finset.nat.sum_antidiagonal_eq_sum_range_succ f],
  have h: ∀ k:ℕ, (k ∈ (finset.range q.succ)) →
   (f k (q - k) = (-1) ^ k * bernoulli k * ↑(q.succ.choose k) *
  ↑n ^ (q + 1 - k) / (↑(q.factorial) * (↑q + 1)) ):=
  begin
    simp only [finset.mem_range],
    intros k g,
    simp [f],
    ring,
    have hfac:
    ((↑(q - k) + 1) * ↑((q - k).factorial))⁻¹ * ↑n ^ (q - k).succ * (↑(k.factorial))⁻¹ =
  (↑(q.factorial) * (↑q + (1:ℚ )))⁻¹ * ↑n ^ (q + 1 - k) * ↑(q.succ.choose k):=
    begin
      have exp_succ: (q - k).succ = (q + 1 - k) := by omega,
      rw [exp_succ],
      have h_choose: (q.succ.choose k) =
      ((q + 1).factorial)/((k.factorial)*(q + 1 - k).factorial) :=
      begin
        rw nat.choose_eq_factorial_div_factorial,
        exact le_of_lt g,
      end,
      rw [h_choose],
      have h_exp_fac2: (q + 1 - k).factorial
        =((((q - k)).factorial)*(q - k +1)) :=
        begin
          have hqk1: q -k + 1 = (q - k).succ := by refl,
          rw [hqk1],
          rw [nat.mul_comm],
          rw [←nat.factorial_succ],
          have hq1: q + 1 - k = (q - k).succ := eq.symm exp_succ,
          rw [hq1],
        end,
      rw [h_exp_fac2],
      rw [mul_comm ↑(q.factorial)],
      have hqqsucc: (q:ℚ)  + 1 = q.succ := by rw [←nat.cast_succ],
      have hqqsucc': (q:ℕ)  + 1 = q.succ := by simp,
      simp only [hqqsucc],
      have hcoeq: ((q.succ):ℚ) * ((q.factorial):ℚ) =(((q.succ.factorial:ℕ)):ℚ) := by norm_cast,
      rw [hcoeq],
      rw [mul_comm (↑(q.succ.factorial))⁻¹ ],
      rw [mul_assoc ((n:ℚ) ^ (q + 1 - k))],
      simp only [div_eq_mul_inv],
      rw [hqqsucc'],
      have hqsuccnezero: q.succ ≠ 0 := by contradiction,
      rw [mul_assoc ],
      rw [inv_eq_one_div ↑(q.succ.factorial)],
      rw ← division_def,
      rw div_eq_mul_one_div,
      have hfacprod:  ↑(k.factorial * (q + 1 - k).factorial) ≠  0 := 
      begin
        have hmfacnezero: k.factorial ≠ 0:= ne_of_gt k.factorial_pos,
        have hnmfacnezero: (q + 1 - k).factorial ≠ 0 :=
          begin
           have hm: ∃ m, m = q + 1 - k:=
            begin
              simp only [exists_apply_eq_apply],
           end,
          refine ne_of_gt _,
          cases hm with m hm,
          have hmfac: m.factorial >0 :=  m.factorial_pos,
          rw hm at hmfac,
          exact hmfac,
        end,
        have hnn: k.factorial * (q + 1 - k).factorial ≠ 0 := mul_ne_zero hmfacnezero hnmfacnezero,
        simp [hnn],
      end,
      rw ← h_exp_fac2,
      rw nat.cast_dvd,
      simp only [← mul_div_assoc],
      rw one_div_mul_cancel,
      rw ← nat.cast_add_one,
      rw ← nat.cast_mul,
      rw mul_comm (q - k + 1) _,
      rw ← h_exp_fac2,
      rw mul_comm,
      rw ← division_def,
      rw div_div_eq_div_mul,
      rw nat.cast_mul,
      rw mul_comm (↑(k.factorial)) _,
      simp,
      rw not_or_distrib,
      split,
      refine ne.elim _,
      exact nat.cast_add_one_ne_zero q,
      refine ne.elim _,
      exact nat.factorial_ne_zero q,
      rw hqqsucc',
      exact nat.factorial_mul_factorial_dvd_factorial (nat.le_of_lt g),
      simp [hfacprod],
      simp [nat.factorial_ne_zero],
      end,
    rw [hfac],
  end,
  refine finset.sum_congr rfl _,
  exact h,
end

theorem power_series_equal (n:ℕ):
(power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) =
 (power_series.mk (λ p,((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1)))))) :=
 begin
   let left := (power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) ,
   have hleft: left =(power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) := by refl,
   let right := (power_series.mk (λ p,((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1)))))),
   have hright: right =(power_series.mk (λ p,((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1)))))) := by refl,
  have h: (exp ℚ - 1)*left = (exp ℚ - 1)*right :=
  begin
   rw [hleft],
   rw [←expand_tonelli],
   have hfin: (finset.range n).sum (λ (k : ℕ),
   mk (λ (n : ℕ), (k:ℚ) ^ n / ↑(n.factorial))) =
   (finset.range n).sum(λ k, expk k) :=
   begin
     simp [expkrw],
   end,
   rw [hfin],
   rw [special_sum_inf_geo_seq],
   rw [right_series],
   rw [←bernoulli_power_series'],
   rw [mul_assoc],
   rw [cauchy_prod],
  end,
  have hexpnezero: (exp ℚ - 1) ≠ 0 :=
  begin
    rw [exp],
    simp [power_series.ext_iff],
    use 1,
    simp,
  end,
  apply mul_left_cancel' hexpnezero h,
 end

theorem faulhaber_long' (n: ℕ): ∀p,
(coeff ℚ p) (power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) =
 (coeff ℚ p) (power_series.mk (λp,
 ((finset.range p.succ).sum(λ i, (-1)^i*(bernoulli i)*
 (p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1))))))  :=
 begin
   exact power_series.ext_iff.mp (power_series_equal n),
 end

theorem faulhaber' (n p:ℕ):
(finset.range n).sum(λk, (k:ℚ)^p) =
((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/p.succ)) :=
begin
 have hfaulhaber_long': (coeff ℚ p) (power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) =
 (coeff ℚ p) (power_series.mk (λp,
 ((finset.range p.succ).sum(λ i, (-1)^i*(bernoulli i)*
 (p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1)) )))) := faulhaber_long' n p,
 simp only [power_series.coeff_mk] at hfaulhaber_long',
 rw [div_eq_mul_inv] at hfaulhaber_long',
 rw [mul_comm ((p.factorial):ℚ ) _] at hfaulhaber_long',
 have hfl: (finset.range n).sum (λ (k : ℕ), ↑k ^ p) * (↑(p.factorial))⁻¹ =
  ((finset.range p.succ).sum
    (λ (i : ℕ), (-1) ^ i * bernoulli i * ↑(p.succ.choose i) * ↑n ^ (p + 1 - i))
    / ((↑p + 1) * ↑(p.factorial))) :=
    begin
      simp [hfaulhaber_long'],
      rw div_eq_mul_one_div,
      simp [finset.sum_mul],
      refine finset.sum_congr  _ _,
      refl,
      intro k,
      intro hk,
      rw div_eq_mul_one_div,
      rw [one_div],
    end,
 clear hfaulhaber_long',
 rw [div_mul_eq_div_mul_one_div ] at hfl,
 simp at hfl,
 have hp: (p.factorial) ≠ 0:= nat.factorial_ne_zero p,
 cases hfl,
 simp,
 rw [hfl],
 rw div_eq_mul_one_div,
 simp [finset.sum_mul],
 refine finset.sum_congr  _ _,
 refl,
 intro k,
 intro hk,
 rw div_eq_mul_one_div,
 rw [one_div],
 by_contradiction,
 exact hp hfl,
end

lemma bernoulli_fst_snd (n:ℕ): 1 < n → bernoulli n = (-1)^n * bernoulli n :=
begin
  intro hn,
  by_cases odd n,
  rw [bernoulli_odd_eq_zero h hn],
  simp,
  have heven: even n := nat.even_iff_not_odd.mpr h,
  have heven_power: even n → (-(1:ℚ))^n = 1 := nat.neg_one_pow_of_even,
  rw [heven_power heven],
  simp,
end

lemma faulhaber (n:ℕ) (p:ℕ) (hp: 0 <p):
(finset.range n.succ).sum (λ k, ↑k^p) =
((finset.range p.succ).sum (λ j, ((bernoulli j)*(nat.choose p.succ j))
*n^(p + 1 - j)/(p.succ)))  :=
begin
  rw [finset.sum_range_succ],
  rw [faulhaber' n p],
  have h2: (1:ℕ).succ ≤ p.succ :=
  begin
    apply nat.succ_le_succ,
    exact nat.one_le_of_lt hp,
  end,
  rw [finset.range_eq_Ico],
  have hsplit:
  finset.Ico 0 (1:ℕ).succ ∪ finset.Ico (1:ℕ).succ p.succ =
  finset.Ico 0 p.succ :=
  finset.Ico.union_consecutive (nat.zero_le (1:ℕ).succ)   h2,
  have hdisjoint:
  disjoint (finset.Ico 0 (1:ℕ).succ)  (finset.Ico (1:ℕ).succ p.succ) :=
  finset.Ico.disjoint_consecutive 0 (1:ℕ).succ p.succ,
  rw [←hsplit],
  rw [finset.sum_union hdisjoint],
  rw [←finset.range_eq_Ico],
  rw [finset.sum_range_succ],
  have h_zeroth_summand:
  (finset.range (1:ℕ)).sum (λ (x : ℕ), (-1) ^ x * bernoulli x *
  ↑(p.succ.choose x) * ↑n ^ (p + 1 - x) / ↑(p.succ)) =
  (finset.range 1).sum (λ (x : ℕ), bernoulli x *
  ↑(p.succ.choose x) * ↑n ^ (p + 1 - x) / ↑(p.succ)) :=
  begin
    simp,
  end,
  have h_fst_summand'':
  (n:ℚ)^p*(p.succ) + (((-1) ^ 1)  * (bernoulli 1) * (p.succ.choose 1) * n ^(p + 1 - 1)) =
  ((bernoulli 1) * (p.succ.choose 1) * n ^(p + 1 - 1)) :=
  begin
    simp,
    ring,
  end,
   have h_fst_summand':
  ((n:ℚ)^p*(p.succ) + (((-1) ^ 1) * (bernoulli 1) * (p.succ.choose 1) * n ^(p + 1 - 1)))/p.succ =
  ((bernoulli 1) * (p.succ.choose 1) * n ^(p + 1 - 1))/p.succ :=
  begin
    rw [←h_fst_summand''],
  end,
   have h_fst_summand:
  (n:ℚ)^p + (((-1) ^ 1) * (bernoulli 1) * (p.succ.choose 1) * n ^(p + 1 - 1))/p.succ =
  ((bernoulli 1) * (p.succ.choose 1) * n ^(p + 1 - 1))/p.succ :=
  begin
    rw [←h_fst_summand'],
    rw [eq_div_iff_mul_eq],
    simp,
    rw [add_mul],
    simp,
    rw [neg_div],
    rw [neg_mul_eq_neg_mul_symm],
    rw [mul_assoc],
    have hpnezero: (p.succ:ℚ)  ≠ 0 :=
    begin
      apply ne_of_gt,
      simp,
      exact nat.cast_add_one_pos _,
    end,
    simp [(div_mul_cancel (((↑p + 1) * ↑n ^ p)) hpnezero)],
    { field_simp, ring },
    apply ne_of_gt,
    simp,
    exact nat.cast_add_one_pos _,
  end,
  have h_large_summands:
  (finset.Ico (1:ℕ).succ p.succ).sum  (λ (x : ℕ), (-1) ^ x * bernoulli x
  * ↑(p.succ.choose x) * ↑n ^ (p + 1 - x) / ↑(p.succ)) =
  (finset.Ico (1:ℕ).succ p.succ).sum  (λ (x : ℕ), bernoulli x
  * ↑(p.succ.choose x) * ↑n ^ (p + 1 - x) / ↑(p.succ)) :=
  begin
    refine finset.sum_congr _ _,
    refl,
    intros x hin,
    have h1x: 1 < x :=
    begin
      rw [finset.Ico.mem] at hin,
      exact_mod_cast hin.1,
    end,
    rw [←bernoulli_fst_snd x h1x],
  end,
  simp only [←add_assoc],
  rw [h_zeroth_summand],
  rw [h_fst_summand],
  rw [h_large_summands],
  simp only [←(finset.sum_range_succ (λ (x : ℕ), bernoulli x * ↑(p.succ.choose x) *
   ↑n ^ (p + 1 - x) / ↑(p.succ)) 1)],
   rw [finset.range_eq_Ico],
   have honeone: 1 + 1 = (1:ℕ).succ := rfl,
   rw [honeone],
   rw [←finset.sum_union hdisjoint],
end
