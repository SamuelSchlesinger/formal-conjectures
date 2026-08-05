/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Ramanujan τ-function

There are two conjectures related to the Ramanujan τ-function:

- Ramanujan-Petersson conjecture: For every prime `p`, the absolute value of the
  Ramanujan τ-function at `p` is bounded by `2 * p^(11/2)`.
- Lehmer's conjecture: The Ramanujan τ-function is never zero for any positive integer `n`.

*References:*
- [Ramanujan-Petersson conjecture](https://en.wikipedia.org/wiki/Ramanujan%E2%80%93Petersson_conjecture)
- [Lehmer's conjecture](https://en.wikipedia.org/wiki/Ramanujan_tau_function#Conjectures_on_the_tau_function)
-/

namespace RamanujanTau

open PowerSeries PowerSeries.WithPiTopology

noncomputable def Δ : PowerSeries ℤ := X * ∏' (n : ℕ+), (1 - X ^ (n : ℕ)) ^ 24

noncomputable def τ (n : ℕ) : ℤ := PowerSeries.coeff n Δ


@[category API, AMS 11]
lemma multipliable : Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) := by
  sorry

@[category test, AMS 11]
lemma τ_zero : τ 0 = 0 := by simp [τ, Δ]

@[category test, AMS 11]
lemma τ_one : τ 1 = 1 := by
  obtain ⟨i, hi⟩ := by simpa using ((continuous_constantCoeff ℤ).tendsto _).comp multipliable.hasProd
  simp [τ, Δ, hi i]

@[category test, AMS 11]
lemma τ_two : τ 2 = -24 := by
  let factor (n : ℕ+) : PowerSeries ℤ := (1 - X ^ (n : ℕ)) ^ 24
  have factor_constantCoeff (n : ℕ+) : constantCoeff (factor n) = 1 := by
    simp [factor]
  have factor_coeff_one (n : ℕ+) :
      coeff 1 (factor n) = if n = 1 then -24 else 0 := by
    by_cases h : n = 1
    · subst n
      norm_num [factor, coeff_one_pow, coeff_X_pow]
    · have hn : (n : ℕ) ≠ 1 := by simpa using h
      simp [factor, coeff_one_pow, coeff_X_pow, h, hn.symm]
  have coeff_one_prod (s : Finset ℕ+) :
      coeff 1 (∏ n ∈ s, factor n) = if 1 ∈ s then -24 else 0 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, coeff_one_mul, ih]
        by_cases h : a = 1
        · subst a
          simp [factor_constantCoeff, factor_coeff_one, ha]
        · simp [factor_constantCoeff, factor_coeff_one, h, Ne.symm h]
  have hprod : Multipliable factor := by
    simpa [factor] using multipliable
  have hlim : Filter.Tendsto
      (fun s : Finset ℕ+ ↦ coeff 1 (∏ n ∈ s, factor n)) Filter.atTop
      (nhds (coeff 1 (∏' n : ℕ+, factor n))) :=
    ((continuous_coeff ℤ 1).tendsto _).comp hprod.hasProd
  have hconst : Filter.Tendsto
      (fun s : Finset ℕ+ ↦ coeff 1 (∏ n ∈ s, factor n)) Filter.atTop (nhds (-24)) :=
    tendsto_atTop_of_eventually_const (i₀ := {1}) fun s hs ↦ by
      rw [coeff_one_prod]
      have h1 : (1 : ℕ+) ∈ s := Finset.singleton_subset_iff.mp hs
      simp only [if_pos h1]
  have coeff_one_tprod : coeff 1 (∏' n : ℕ+, factor n) = -24 :=
    tendsto_nhds_unique hlim hconst
  simpa [τ, Δ, factor] using coeff_one_tprod


/-- The Ramanujan-Petersson conjecture: $|\tau(p)| \le 2 p^{11/2}$ for primes $p$. -/
@[category research solved, AMS 11]
theorem ramanujan_petersson : ∀ p : ℕ, Prime p → abs (τ p) ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2) := by
  sorry

/-- Lehmer's conjecture: $\tau(n) \ne 0$ for all $n > 0$. -/
@[category research open, AMS 11]
theorem lehmer_ramanujan_tau : ∀ n > 0, τ n ≠ 0 := by
  sorry

end RamanujanTau
