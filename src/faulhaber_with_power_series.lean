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

import ring_theory.power_series.basic

open power_series


#check exp ℚ
def expk (k:ℕ) : power_series ℚ := power_series.mk (λ n, (k:ℚ)^n / n.factorial)

lemma power_series_addition (ha hb: ℕ → ℚ):
power_series.mk(ha) + power_series.mk(hb) =
power_series.mk(λ z, (ha z) + (hb z)) :=
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

theorem sum_inf_geo_seq (n:ℕ):
(finset.range n).sum(λ k, expk k) * (1 - exp ℚ) = (1 - expk n) :=
begin
  sorry,
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
  power_series.mk (λ n,
  ((-1)^n* bernoulli n / nat.factorial n : ℚ)) * (exp ℚ - 1) = X :=
begin
  sorry,
end

theorem cauchy_prod (n:ℕ):
power_series.mk (λ p, (n:ℚ)^p.succ/(p.succ.factorial)) *
power_series.mk (λ n,
  ((-1)^n* bernoulli n / nat.factorial n : ℚ)) =
 power_series.mk (λp,
 (1:ℚ)/((p.factorial)*(p + 1))*((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)))) := by sorry


theorem power_series_equal (n:ℕ):
power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial)) =
 power_series.mk (λp,
 (1:ℚ)/((p.factorial)*(p + 1))*((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)))) := by sorry

theorem faulhaber_long' (n:ℕ): ∀ p,
(coeff ℚ p) (power_series.mk (λ p, (finset.range n).sum(λk, (k:ℚ)^p)/(p.factorial))) =
 (coeff ℚ p) (power_series.mk (λp,
 (1:ℚ)/((p.factorial)*(p + 1))*((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)))))  :=
 begin
   exact power_series.ext_iff.mp (power_series_equal n),
 end

theorem faulhaber' (n p :ℕ):
(finset.range n).sum(λk, (k:ℚ)^p) =
((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i)/p.succ)) :=
begin
  sorry
end

lemma one_minus_b1: 1 - bernoulli 1 = bernoulli 1 :=
begin
  simp,
  ring,
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
