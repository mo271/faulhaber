import algebra.module.linear_map
import ring_theory.power_series.basic

variables {σ R : Type*}
variables (R) [semiring R]
/-
theorem linear_map_test :
is_linear_map  R (λ (z:R), z) :=
begin
  refine {map_add := _, map_smul := _},
  intros,
  simp,
  intros,
  simp,
end
-/
theorem pow_series_mk_is_lin_map (R :Type) [semiring R]:
is_linear_map R (λ (z:power_series R), z) :=
begin
  refine {map_add := _, map_smul := _},
  repeat {simp only [forall_const, eq_self_iff_true]},
end

