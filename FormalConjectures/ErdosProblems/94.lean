/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 94

*References:*
- [erdosproblems.com/94](https://www.erdosproblems.com/94)
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*. Eureka
  (1992), 44-48.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős, I
  (1997), 47-67.
- [LeTh95] Lefmann, Hanno and Thiele, Torsten, *Point sets with distinct distances*. Combinatorica
  (1995), 379-408.
-/

open Filter EuclideanGeometry

namespace Erdos94

/-- The regular $n$-gon inscribed in the unit circle. -/
noncomputable def regularNGon (n : ℕ) : Finset ℝ² :=
  (Finset.range n).image fun k : ℕ =>
    !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

/--
Suppose $n$ points in $\mathbb{R}^2$ determine a convex polygon and the set of distances between
them is $\{u_1,\ldots,u_t\}$. Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs of
points. Then
$$\sum_i f(u_i)^2 \ll n^3.$$

In [Er97c] Erdős claims that Fishburn solved this, but gives no reference.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos94.lean"]
theorem erdos_94 : ∃ C > (0 : ℝ), ∀ P : Finset ℝ², ConvexIndep (P : Set ℝ²) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/--
Note it is trivial that $\sum f(u_i)=\binom{n}{2}$.
-/
@[category test, AMS 5 52]
theorem erdos_94.variants.sum_multiplicity (P : Finset ℝ²) :
    ∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2 := by
  classical
  let f : ℝ² × ℝ² → ℝ := fun pair => dist pair.1 pair.2
  have h_two_mul (u : ℝ) :
      2 * ((P.offDiag.filter fun pair => f pair = u).image Sym2.mk).card =
        (P.offDiag.filter fun pair => f pair = u).card := by
    rw [Finset.card_eq_sum_card_image (Sym2.mk : ℝ² × ℝ² → Sym2 ℝ²),
      Finset.sum_const_nat (Sym2.ind _), mul_comm]
    rintro x y hxy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_offDiag] at hxy
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb, hab⟩, hd⟩, hmk⟩ := hxy
    have hxy : x ∈ P ∧ y ∈ P ∧ x ≠ y ∧ f (x, y) = u := by
      obtain h | h := Sym2.mk_eq_mk_iff.1 hmk
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ha, hb, hab, hd⟩
      · simp only [Prod.mk.injEq, Prod.swap_prod_mk] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hb, ha, hab.symm, by simpa [f, dist_comm] using hd⟩
    have hfiber :
        {z ∈ P.offDiag.filter (fun pair => f pair = u) |
            Sym2.mk z = s(x, y)} = {(x, y), (y, x)} := by
      ext ⟨x₁, y₁⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
        Finset.mem_singleton, Sym2.eq_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨_, hEq⟩
        exact hEq
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨⟨hxy.1, hxy.2.1, hxy.2.2.1⟩, hxy.2.2.2⟩,
            Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨⟨⟨hxy.2.1, hxy.1, hxy.2.2.1.symm⟩,
            by simpa [f, dist_comm] using hxy.2.2.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    rw [hfiber, Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hxy.2.2.1]
  have h_even (u : ℝ) : 2 ∣ (P.offDiag.filter fun pair => f pair = u).card :=
    ⟨((P.offDiag.filter fun pair => f pair = u).image Sym2.mk).card,
      (h_two_mul u).symm⟩
  change ∑ u ∈ P.offDiag.image f,
      (P.offDiag.filter fun pair => f pair = u).card / 2 = P.card.choose 2
  rw [← Nat.sum_div (fun u _ => h_even u), ← Finset.card_eq_sum_card_image]
  simp [Finset.offDiag_card, Nat.choose_two_right, Nat.mul_sub_left_distrib]

/--
Lefmann and Theile [LeTh95] prove a stronger version of this question, that
$$\sum_i f(u_i)^2 \ll n^3$$
under the weaker assumption that no three points are on a line.
-/
@[category research solved, AMS 5 52]
theorem erdos_94.variants.no_three_on_a_line : ∃ C > (0 : ℝ), ∀ P : Finset ℝ²,
    NonTrilinear (P : Set ℝ²) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/--
Erdős and Fishburn also make the stronger conjecture that $\sum f(u_i)^2$ is maximal for the
regular $n$-gon (for large enough $n$).
-/
@[category research open, AMS 5 52]
theorem erdos_94.variants.regular_ngon : ∀ᶠ n : ℕ in atTop, ∀ P : Finset ℝ²,
    P.card = n → ConvexIndep (P : Set ℝ²) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
      ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 := by
  sorry

end Erdos94
