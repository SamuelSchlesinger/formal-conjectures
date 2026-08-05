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
# Conjectures associated with A063880

A063880 lists numbers $n$ such that $\sigma(n) = 2 \cdot \text{usigma}(n)$, where $\sigma(n)$ is the
sum of all divisors and $\text{usigma}(n)$ is the sum of unitary divisors.

Equivalently, these are numbers whose unitary and non-unitary divisors have equal sum.

The conjectures state that all members satisfy $n \equiv 108 \pmod{216}$, and that all
primitive terms (those whose proper divisors aren't in the sequence) are powerful numbers,
with $108$ being the only primitive term.

*References:* [A63880](https://oeis.org/A63880)
-/

namespace OeisA63880

open scoped ArithmeticFunction.sigma

/-- The set of unitary divisors of $n$: divisors $d$ such that $\gcd(d, n/d) = 1$. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of unitary divisors of $n$, denoted $\text{usigma}(n)$. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A number $n$ is in the sequence A063880 if $\sigma(n) = 2 \cdot \text{usigma}(n)$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

/-- A term $n$ is primitive if no proper divisor of $n$ is in the sequence. -/
abbrev IsPrimitiveTerm (n : ℕ) : Prop := {n | A n}.IsPrimitive n

/-- $108$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_108 : A 108 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $540$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_540 : A 540 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $756$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_756 : A 756 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $108$ is a primitive term. -/
@[category test, AMS 11]
theorem isPrimitiveTerm_108 : IsPrimitiveTerm 108 := by
  rw [IsPrimitiveTerm, Set.isPrimitive_iff]
  refine ⟨a_108, ?_⟩
  intro d hd
  have ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  interval_cases d <;> simp_all [A] <;> decide

/-- All members of the sequence satisfy $n \equiv 108 \pmod{216}$. -/
@[category research open, AMS 11]
theorem mod_216_of_a {n : ℕ} (h : A n) : n % 216 = 108 := by
  sorry

/-- Products of unitary divisors of coprime positive numbers are unitary divisors. -/
@[category API, AMS 11]
private lemma mem_unitaryDivisors_mul {m n a b : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (ha : a ∈ unitaryDivisors m) (hb : b ∈ unitaryDivisors n) :
    a * b ∈ unitaryDivisors (m * n) := by
  rw [unitaryDivisors, Finset.mem_filter] at ha hb ⊢
  have ham : a ∣ m := (Nat.mem_divisors.mp ha.1).1
  have hbn : b ∣ n := (Nat.mem_divisors.mp hb.1).1
  refine ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul ham hbn, Nat.mul_ne_zero hm.ne' hn.ne'⟩, ?_⟩
  rw [← Nat.div_mul_div_comm ham hbn]
  have han : a.Coprime (n / b) :=
    Nat.Coprime.of_dvd ham (Nat.div_dvd_of_dvd hbn) hcop
  have hbm : b.Coprime (m / a) :=
    Nat.Coprime.of_dvd hbn (Nat.div_dvd_of_dvd ham) hcop.symm
  exact (ha.2.mul_left hbm).mul_right (han.mul_left hb.2)

/-- A unitary divisor of a coprime product splits into unitary divisors via gcd. -/
@[category API, AMS 11]
private lemma gcd_pair_mem_unitaryDivisors {m n d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (hd : d ∈ unitaryDivisors (m * n)) :
    d.gcd m ∈ unitaryDivisors m ∧ d.gcd n ∈ unitaryDivisors n := by
  rw [unitaryDivisors, Finset.mem_filter] at hd
  have hdvd : d ∣ m * n := (Nat.mem_divisors.mp hd.1).1
  have hprod : d.gcd m * d.gcd n = d :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).2 hdvd
  have ham : d.gcd m ∣ m := Nat.gcd_dvd_right d m
  have hbn : d.gcd n ∣ n := Nat.gcd_dvd_right d n
  have had : d.gcd m ∣ d := Nat.gcd_dvd_left d m
  have hbd : d.gcd n ∣ d := Nat.gcd_dvd_left d n
  have hquot : m / d.gcd m * (n / d.gcd n) = m * n / d := by
    rw [Nat.div_mul_div_comm ham hbn, hprod]
  constructor
  · rw [unitaryDivisors, Finset.mem_filter]
    refine ⟨Nat.mem_divisors.mpr ⟨ham, hm.ne'⟩, ?_⟩
    apply Nat.Coprime.of_dvd_right _ (Nat.Coprime.of_dvd_left had hd.2)
    exact ⟨n / d.gcd n, hquot.symm⟩
  · rw [unitaryDivisors, Finset.mem_filter]
    refine ⟨Nat.mem_divisors.mpr ⟨hbn, hn.ne'⟩, ?_⟩
    apply Nat.Coprime.of_dvd_right _ (Nat.Coprime.of_dvd_left hbd hd.2)
    exact ⟨m / d.gcd m, hquot.symm.trans (Nat.mul_comm _ _)⟩

/-- Unitary divisors of a coprime product are products of unitary divisors. -/
@[category API, AMS 11]
private lemma unitaryDivisors_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) :
    unitaryDivisors (m * n) =
      (unitaryDivisors m ×ˢ unitaryDivisors n).image fun ab ↦ ab.1 * ab.2 := by
  ext d
  simp only [Finset.mem_image, Finset.mem_product]
  constructor
  · intro hd
    refine ⟨(d.gcd m, d.gcd n), gcd_pair_mem_unitaryDivisors hm hn hcop hd, ?_⟩
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).2
      ((Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1)
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact mem_unitaryDivisors_mul hm hn hcop ha hb

/-- The sum of unitary divisors is multiplicative on coprime positive numbers. -/
@[category API, AMS 11]
private lemma usigma_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    usigma (m * n) = usigma m * usigma n := by
  have hinj : ∀ x ∈ unitaryDivisors m ×ˢ unitaryDivisors n,
      ∀ y ∈ unitaryDivisors m ×ˢ unitaryDivisors n,
        x.1 * x.2 = y.1 * y.2 → x = y := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
    rw [Finset.mem_product] at hab hcd
    rcases hab with ⟨ha, hb⟩
    rcases hcd with ⟨hc, hd⟩
    rw [unitaryDivisors, Finset.mem_filter] at ha hb hc hd
    have ham : a ∣ m := (Nat.mem_divisors.mp ha.1).1
    have hcm : c ∣ m := (Nat.mem_divisors.mp hc.1).1
    have hbn : b ∣ n := (Nat.mem_divisors.mp hb.1).1
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd.1).1
    have hbm : b.Coprime m := Nat.Coprime.of_dvd_left hbn hcop.symm
    have hdm : d.Coprime m := Nat.Coprime.of_dvd_left hdn hcop.symm
    have han : a.Coprime n := Nat.Coprime.of_dvd_left ham hcop
    have hcn : c.Coprime n := Nat.Coprime.of_dvd_left hcm hcop
    have ha_gcd : (a * b).gcd m = a := by
      rw [mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd hbm ham
    have hc_gcd : (c * d).gcd m = c := by
      rw [mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd hdm hcm
    have hb_gcd : (a * b).gcd n = b := Nat.gcd_mul_of_coprime_of_dvd han hbn
    have hd_gcd : (c * d).gcd n = d := Nat.gcd_mul_of_coprime_of_dvd hcn hdn
    have hac : a = c := by rw [← ha_gcd, heq, hc_gcd]
    have hbd : b = d := by rw [← hb_gcd, heq, hd_gcd]
    simp [hac, hbd]
  rw [usigma, unitaryDivisors_mul hm hn hcop, Finset.sum_image hinj, usigma, usigma]
  simp only [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- All primitive terms are powerful numbers. -/
@[category textbook, AMS 11]
theorem powerful_of_isPrimitiveTerm {n : ℕ} (h : IsPrimitiveTerm n) : n.Powerful := by
  change ∀ p ∈ n.primeFactors, p ^ 2 ∣ n
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
  by_contra hpsq
  let m := n / p
  have hn_pos : 0 < n := h.mem.1
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn_pos hpn) hp_prime.pos
  have hnm : n = p * m := (Nat.mul_div_cancel' hpn).symm
  have hpm : p.Coprime m := hp_prime.coprime_iff_not_dvd.mpr fun hpm ↦ by
    apply hpsq
    rw [hnm, pow_two]
    exact Nat.mul_dvd_mul_left p hpm
  have hm_lt : m < n := by
    rw [hnm]
    nlinarith [hp_prime.one_lt]
  apply h.not_mem_of_dvd_of_lt (Nat.div_dvd_of_dvd hpn) hm_lt
  have hAn : A n := h.mem
  change 0 < m ∧ σ 1 m = 2 * usigma m
  refine ⟨hm_pos, ?_⟩
  change 0 < n ∧ σ 1 n = 2 * usigma n at hAn
  rw [hnm, ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    ArithmeticFunction.isMultiplicative_sigma hpm, usigma_mul hp_prime.pos hm_pos hpm] at hAn
  have hsigma_p : σ 1 p = p + 1 := by
    simpa [add_comm] using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp_prime
  have husigma_p : usigma p = p + 1 := by
    have hfilter : ({1, p} : Finset ℕ).filter (fun d ↦ d.Coprime (p / d)) = {1, p} := by
      apply Finset.filter_eq_self.mpr
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with hd | hd
      · subst d
        simp
      · subst d
        rw [Nat.div_self hp_prime.pos]
        exact Nat.coprime_one_right _
    rw [usigma, unitaryDivisors, hp_prime.divisors, hfilter]
    rw [Finset.sum_pair hp_prime.ne_one.symm]
    omega
  rw [hsigma_p, husigma_p] at hAn
  have hcancel : (p + 1) * σ 1 m = (p + 1) * (2 * usigma m) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hAn.2
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p + 1) hcancel

/-- $108$ is the only primitive term. -/
@[category research open, AMS 11]
theorem unique_primitive_108 {n : ℕ} (h : IsPrimitiveTerm n) : n = 108 := by
  sorry

/-- If $m$ is a primitive term and $s$ is squarefree with $\gcd(m, s) = 1$, then $m \cdot s$
is in the sequence. -/
@[category textbook, AMS 11]
theorem a_of_primitive_mul_squarefree (m s : ℕ) (hm : IsPrimitiveTerm m)
    (hs : Squarefree s) (hcoprime : m.Coprime s) : A (m * s) := by
  sorry

/-- Non-primitive terms have the form $m \cdot s$ where $m$ is primitive and $s$ is
squarefree with $\gcd(m, s) = 1$. -/
@[category research solved, AMS 11]
theorem exists_primitive_of_a {n : ℕ} (h : A n) :
    ∃ m s, IsPrimitiveTerm m ∧ Squarefree s ∧ m.Coprime s ∧ n = m * s := by
  sorry

end OeisA63880
