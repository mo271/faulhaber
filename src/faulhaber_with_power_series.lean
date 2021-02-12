
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

theorem expand_tonelli (n:ℕ ):
(finset.range n).sum(λ k, expk k) =
power_series.mk (λ p, (finset.range n).sum(λ k, k^p)/p.factorial) := by sorry

theorem sum_inf_geo_seq (n:ℕ):
(finset.range n).sum(λ k, expk k) * (1 - exp ℚ) = (1 - expk n) := by sorry

theorem expand_fraction (n:ℕ):
(1 - expk n) * X * (exp ℚ - 1)  = (1 - exp ℚ) * (expk n - 1) * X := by sorry

theorem right_series (n:ℕ):
(expk n - 1) = X*power_series.mk (λ p, n^p.succ/(p.succ.factorial)) := by sorry

theorem bernoulli_power_series':
  power_series.mk (λ n,
  ((-1)^n* bernoulli n / nat.factorial n : ℚ)) * (exp ℚ - 1) = X := by sorry

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

lemma faulhaber (n:ℕ) (p:ℕ):
(finset.range n.succ).sum (λ k, ↑k^p) =
((finset.range p.succ).sum (λ j, ((bernoulli j)*(nat.choose p.succ j))
*n^(p + 1 - j)))/(p.succ)  :=
begin
  sorry,
end
