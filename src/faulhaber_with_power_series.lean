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

import ring_theory.power_series.basic

open power_series

lemma test:(constant_coeff ℚ) ((exp ℚ - 1) * X) = 0 :=
begin
  simp,
end

#check exp ℚ
def expk (k:ℕ) : power_series ℚ := power_series.mk (λ n, (k:ℚ)^n / n.factorial)


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



theorem sum_inf_geo_seq (n:ℕ):
(finset.range n).sum(λ k, expk k) * (1 - exp ℚ) = (1 - expk n) :=
begin
  ext,
  rw [power_series.coeff_mul],

end



theorem expand_fraction (n:ℕ):
(1 - expk n) * X * (exp ℚ - 1)  = (1 - exp ℚ) * (expk n - 1) * X :=
begin
  ring,
end

theorem right_series (n:ℕ):
(expk n - 1) = X*power_series.mk (λ p, n^p.succ/(p.succ.factorial)) :=
begin
  rw [power_series.X, mul_comm],
  sorry,
end

theorem bernoulli_power_series':
  (exp ℚ - 1) * power_series.mk (λ n,
  ((-1)^n* bernoulli n / nat.factorial n : ℚ)) = X :=
begin
  sorry,
end


lemma reduce_expk (n:ℕ ) {M: power_series ℚ}:
( (exp ℚ - 1) * M = ((expk n) - 1)) → (M = (finset.range n).sum(λ k, expk k)):=
begin
  assume h,
  rw [power_series.ext_iff] at h ⊢,
  intro p,
  have g: (coeff ℚ p) ((exp ℚ - 1) * M) = (coeff ℚ p) (expk n - 1)
  := (h p),
  rw [power_series.coeff_mul] at g,
  rw [power_series_finset],
  simp [expk],
  have hone: (1: (power_series ℚ))  =
  power_series.mk (λ k, if k = 0 then 1 else 0) := by sorry,
  by_cases hp: p<1,
  have hpzero: p = 0 := by linarith,
  simp only [hpzero] at g,
  simp only [expk] at g,
  rw [hone] at g,
  simp only [power_series_subtraction] at g,
  simp [power_series.coeff_mk ] at g,
  sorry, --not true in this case!?
  simp only [expk] at g,
  rw [hone] at g,
  simp only [power_series_subtraction] at g,
  simp [power_series.coeff_mk ] at g,
  sorry,
end

-- this is missing in mathlib?!
theorem power_series_mul_assoc (φ₁ φ₂ φ₃ : (power_series ℚ)) :
φ₁ * (φ₂ * φ₃) = φ₁ * φ₂ * φ₃ :=
begin
  rw mv_power_series.mul_assoc, -- it is not included
end

lemma hprodM (n:ℕ):
((exp ℚ - 1)  *
(power_series.mk (λ n,
  ((-1)^n* bernoulli n / nat.factorial n : ℚ)) *
  (power_series.mk (λ p, (n:ℚ)^p.succ/(p.succ.factorial)))) = ((expk n) - 1)) :=
begin
  rw [power_series_mul_assoc],
  rw [bernoulli_power_series'],
  rw [right_series],
end

theorem expk_sum (n:ℕ):
power_series.mk (λ n,
  ((-1)^n* bernoulli n / nat.factorial n : ℚ))*
  power_series.mk (λ p, (n:ℚ)^p.succ/(p.succ.factorial))  =
  (finset.range n).sum(λ k, expk k) :=
begin
  exact reduce_expk n (hprodM n),
end

--difficultys due to subtraction in nat's
lemma nat_sub (q k:ℕ) (g: k <q.succ): q - k + 1 =q + 1 -k :=
begin
  apply int.coe_nat_inj,
  rw [int.coe_nat_add],
  rw [←int.of_nat_eq_coe],
  rw int.of_nat_sub,
  refine eq.symm _,
  rw [←int.of_nat_eq_coe],
  rw int.of_nat_sub,
  rw int.of_nat_add,
  simp,
  ring,
  rw [nat.succ_eq_add_one] at g,
  exact le_of_lt g,
  rw [nat.succ_eq_add_one] at g,
  rw nat.lt_add_one_iff at g,
  exact g,
end

lemma exp_succ (q k :ℕ) (g: k <q.succ): (q - k).succ = (q + 1 - k) :=
begin
  rw nat.succ_eq_add_one, 
  apply nat_sub,
  exact g,
end

lemma  h_exp_fac2 (q k :ℕ)(g: k <q.succ): (q + 1 - k).factorial = ((((q - k)).factorial)*(q - k + 1)):=
begin
  rw nat_sub,
  rw ← exp_succ,
  rw nat.factorial_succ,
  rw mul_comm,
  exact g,
  exact g,
end

lemma  h_choose (q k :ℕ)(g: k <q.succ): (q.succ.choose k) = ((q + 1).factorial)/((k.factorial)*(q + 1 - k).factorial) := 
begin
  rw nat.choose_eq_factorial_div_factorial,
  exact le_of_lt g,
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
      rw [exp_succ],
      rw [h_choose],
      rw [h_exp_fac2],
      rw [mul_comm],
      ring,
      sorry,
    end,
    rw [hfac],
  end,
  refine finset.sum_congr rfl _,
  exact h,
end

theorem power_series_equal (n:ℕ):
power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial)) =
 power_series.mk (λp,((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/ ((p.factorial)*(p + 1))))) :=
 begin
   rw [←expand_tonelli],
   rw [←cauchy_prod],
   rw [expk_sum],
   refl,
 end

theorem faulhaber_long' (n:ℕ): ∀ p,
(coeff ℚ p) (power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) =
 (coeff ℚ p) (power_series.mk (λp,
 ((finset.range p.succ).sum(λ i, (-1)^i*(bernoulli i)*
 (p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1)) ))))  :=
 begin
   exact power_series.ext_iff.mp (power_series_equal n),
 end

theorem faulhaber' (n p :ℕ):
(finset.range n).sum(λk, (k:ℚ)^p) =
((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/p.succ)) :=
begin
 have hfaulhaber_long': (coeff ℚ p) (power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) =
 (coeff ℚ p) (power_series.mk (λp,
 ((finset.range p.succ).sum(λ i, (-1)^i*(bernoulli i)*
 (p.succ.choose i)*n^(p + 1 - i)/((p.factorial)*(p + 1)) )))) := faulhaber_long' n p,
 simp at hfaulhaber_long',
 have hp: (p.factorial) ≠ 0:= by apply nat.factorial_ne_zero,
 sorry,
end

lemma bernoulli_odd (n:ℕ) (hn: 1 < n): odd n → bernoulli n = 0 :=
begin
  rintro ⟨k, h⟩,
  rw [h],
  rw [bernoulli],
  sorry,
end


lemma bernoulli_fst_snd (n:ℕ): 1 < n → bernoulli n = (-1)^n * bernoulli n :=
begin
  intro hn,
  by_cases odd n,
  rw [bernoulli_odd n hn h],
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
  rw [faulhaber'],
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
