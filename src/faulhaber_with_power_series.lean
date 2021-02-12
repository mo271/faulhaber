
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
  induction n with n h,
  sorry,
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
(1:ℚ)*(p + 1)*((finset.range p.succ).sum(λ i,
 (-1)^i*(bernoulli i)*(p.succ.choose i)*n^(p + 1 - i))) :=
begin
  sorry
end

lemma one_minus_b1: 1 - bernoulli 1 = bernoulli 1 :=
begin
  simp,
  ring,
end

lemma bernoulli_odd (n:ℕ): odd n → bernoulli n = 0 :=
begin
  sorry,
end


lemma bernoulli_fst_snd (n:ℕ): n > 1 → bernoulli n = (-1)^n * bernoulli n :=
begin
  intro h,
  by_cases odd n,
  sorry,
  sorry,
end

lemma faulhaber (n:ℕ) (p:ℕ):
(finset.range n.succ).sum (λ k, ↑k^p) =
((finset.range p.succ).sum (λ j, ((bernoulli j)*(nat.choose p.succ j))
*n^(p + 1 - j)))/(p.succ)  :=
begin
  sorry,
end
