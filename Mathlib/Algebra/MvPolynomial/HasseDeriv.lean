/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Weight

/-!
# Hasse derivatives of multivariate polynomials

This file defines Hasse derivatives for multivariate polynomials. For a multi-index
`i : σ →₀ ℕ`, the map `MvPolynomial.hasseDeriv i` is the `R`-linear endomorphism of
`MvPolynomial σ R` sending the monomial $r X^k$ to $\binom{k}{i} r X^{k-i}$, where
$\binom{k}{i}$ is the multivariate binomial coefficient `MvPolynomial.mvChoose k i`.

## Main declarations

* `MvPolynomial.mvChoose`
* `MvPolynomial.hasseDeriv`
* `MvPolynomial.hasseDeriv_monomial`
* `MvPolynomial.hasseDeriv_coeff`
* `MvPolynomial.hasseDeriv_zero`
* `MvPolynomial.hasseDeriv_comp`
* `MvPolynomial.hasseDeriv_single_one`

## Tags

multivariate polynomial, Hasse derivative
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

open Finsupp
open scoped BigOperators

variable {σ τ R : Type*} [CommSemiring R]

/-- The multivariate binomial coefficient $\binom{k}{i}$. -/
def mvChoose (k i : σ →₀ ℕ) : ℕ :=
  if i ≤ k then k.prod (fun j n ↦ n.choose (i j)) else 0

lemma mvChoose_of_le {k i : σ →₀ ℕ} (h : i ≤ k) :
    mvChoose k i = k.prod (fun j n ↦ n.choose (i j)) := by
  simp [mvChoose, h]

lemma mvChoose_of_not_le {k i : σ →₀ ℕ} (h : ¬ i ≤ k) : mvChoose k i = 0 := by
  simp [mvChoose, h]

@[simp]
lemma mvChoose_zero (k : σ →₀ ℕ) : mvChoose k 0 = 1 := by
  simp [mvChoose, Finsupp.prod]

@[simp]
lemma mvChoose_self (k : σ →₀ ℕ) : mvChoose k k = 1 := by
  classical
  simp [mvChoose, Finsupp.prod]

/-- For a single-coordinate multi-index, `mvChoose` is the usual binomial coefficient. -/
lemma mvChoose_single (k : σ →₀ ℕ) (i : σ) (j : ℕ) :
    mvChoose k (Finsupp.single i j) = Nat.choose (k i) j := by
  classical
  by_cases h : Finsupp.single i j ≤ k
  · have hji : j ≤ k i := Finsupp.single_le_iff.mp h
    rw [mvChoose_of_le (k := k) (i := Finsupp.single i j) h, Finsupp.prod]
    have hprod :
        ∏ x ∈ k.support, Nat.choose (k x) (Finsupp.single i j x) =
          Nat.choose (k i) (Finsupp.single i j i) := by
      refine Finset.prod_eq_single (s := k.support)
        i (fun b _ hb ↦ ?_) ?_
      · have hb0 : Finsupp.single i j b = 0 := by simp [hb]
        simp [hb0]
      · intro hi
        have hk : k i = 0 := Finsupp.notMem_support_iff.mp hi
        have hj : j = 0 := Nat.eq_zero_of_le_zero (by simpa [hk] using hji)
        simp [hk, hj]
    simpa using hprod
  · have hji : k i < j := by
      refine lt_of_not_ge (fun hji ↦ ?_)
      exact h (Finsupp.single_le_iff.mpr hji)
    simp [mvChoose_of_not_le (k := k) (i := Finsupp.single i j) h,
      Nat.choose_eq_zero_of_lt hji]

/-- The symmetry identity $\binom{i + j}{i} = \binom{i + j}{j}$. -/
theorem mvChoose_symm_add (i j : σ →₀ ℕ) :
    mvChoose (i + j) i = mvChoose (i + j) j := by
  classical
  rw [mvChoose_of_le (Finsupp.le_def.2 fun x => Nat.le_add_right _ _),
    mvChoose_of_le (Finsupp.le_def.2 fun x => Nat.le_add_left _ _)]
  simp only [Finsupp.prod, Finsupp.add_apply]
  refine Finset.prod_congr rfl (fun x _hx ↦ ?_)
  simpa using (Nat.choose_symm_add (a := i x) (b := j x))

lemma mvChoose_symm_add_cast (i j : σ →₀ ℕ) :
    (mvChoose (i + j) i : R) = (mvChoose (i + j) j : R) :=
  congrArg (fun n : ℕ => (n : R)) (mvChoose_symm_add (σ := σ) i j)

/-- The identity $\binom{k}{i} \binom{k - i}{j} = \binom{k}{i + j} \binom{i + j}{i}$. -/
theorem mvChoose_mul (k i j : σ →₀ ℕ) :
    mvChoose k i * mvChoose (k - i) j =
      mvChoose k (i + j) * mvChoose (i + j) i := by
  classical
  by_cases hi : i ≤ k
  · by_cases hj : j ≤ k - i
    · have hij : i + j ≤ k := by
        rw [Finsupp.le_def] at hi hj ⊢
        intro x
        have hx : i x + j x ≤ i x + (k x - i x) := Nat.add_le_add_left (hj x) _
        simpa [Finsupp.add_apply, Finsupp.tsub_apply, Nat.add_sub_of_le (hi x)] using hx
      rw [mvChoose_of_le hi, mvChoose_of_le hj, mvChoose_of_le hij,
        mvChoose_of_le (Finsupp.le_def.2 fun x => Nat.le_add_right _ _)]
      have hprod_ki :
          (k - i).prod (fun x n ↦ n.choose (j x)) =
            ∏ x ∈ k.support, (k x - i x).choose (j x) := by
        have h :=
          Finset.prod_subset (Finsupp.support_tsub (f1 := k) (f2 := i))
            (f := fun x ↦ (k x - i x).choose (j x)) ?_
        · simpa [Finsupp.prod, Finsupp.tsub_apply] using h
        · intro x _hxk hxki
          have hx0 : (k - i) x = 0 := Finsupp.notMem_support_iff.mp hxki
          have hx0' : k x - i x = 0 := by simpa [Finsupp.tsub_apply] using hx0
          have hjx : j x = 0 := by
            have : j x ≤ (k - i) x := (Finsupp.le_def.mp hj) x
            exact Nat.eq_zero_of_le_zero (by simpa [hx0] using this)
          simp [hx0', hjx]
      have hprod_ij :
          (i + j).prod (fun x n ↦ n.choose (i x)) =
            ∏ x ∈ k.support, (i x + j x).choose (i x) := by
        have hsupp : (i + j).support ⊆ k.support := by
          intro x hxij
          have hx_ne0 : (i + j) x ≠ 0 := Finsupp.mem_support_iff.mp hxij
          have hx_pos : 0 < (i + j) x := Nat.pos_of_ne_zero hx_ne0
          have hx_le : (i + j) x ≤ k x := (Finsupp.le_def.mp hij) x
          exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (lt_of_lt_of_le hx_pos hx_le))
        have h :=
          Finset.prod_subset hsupp (f := fun x ↦ (i x + j x).choose (i x)) ?_
        · simpa [Finsupp.prod, Finsupp.add_apply] using h
        · intro x _hxk hxij
          have hx0 : (i + j) x = 0 := Finsupp.notMem_support_iff.mp hxij
          obtain ⟨hix, hjx⟩ := Nat.add_eq_zero_iff.mp (by simpa [Finsupp.add_apply] using hx0)
          simp [hix, hjx]
      rw [hprod_ki, hprod_ij]
      simp only [Finsupp.prod, Finsupp.add_apply]
      rw [(Finset.prod_mul_distrib (s := k.support)
            (f := fun x ↦ (k x).choose (i x))
            (g := fun x ↦ (k x - i x).choose (j x))).symm]
      rw [(Finset.prod_mul_distrib (s := k.support)
            (f := fun x ↦ (k x).choose (i x + j x))
            (g := fun x ↦ (i x + j x).choose (i x))).symm]
      refine Finset.prod_congr rfl (fun x hx ↦ ?_)
      simpa [Nat.add_sub_cancel_left] using
        (Nat.choose_mul (n := k x) (k := i x + j x) (s := i x) (Nat.le_add_right _ _)).symm
    · have hij : ¬ i + j ≤ k := by
        intro hij
        apply hj
        rw [Finsupp.le_def] at hij ⊢
        intro x
        have hijx : i x + j x ≤ k x := by simpa [Finsupp.add_apply] using hij x
        have : j x + i x ≤ k x := by simpa [Nat.add_comm] using hijx
        have : j x ≤ k x - i x := Nat.le_sub_of_add_le this
        simpa [Finsupp.tsub_apply] using this
      simp [mvChoose, hi, hj, hij]
  · have hij : ¬ i + j ≤ k := fun hij =>
      hi ((Finsupp.le_def.2 fun x => Nat.le_add_right _ _).trans hij)
    simp [mvChoose, hi, hij]

/-- Over a finite index type, $\binom{k}{i} = \prod_{j : \sigma} \binom{k_j}{i_j}$. -/
lemma mvChoose_eq_prod_choose [Fintype σ] (k i : σ →₀ ℕ) :
    mvChoose k i = ∏ j : σ, (k j).choose (i j) := by
  classical
  by_cases hle : i ≤ k
  · rw [mvChoose_of_le (k := k) (i := i) hle]
    have houtside :
        ∀ x ∈ (Finset.univ : Finset σ), x ∉ k.support → Nat.choose (k x) (i x) = 1 := by
      intro x _hx hxnot
      have hk0 : k x = 0 := Finsupp.notMem_support_iff.mp hxnot
      have hix : i x = 0 := by
        have : i x ≤ k x := (Finsupp.le_def.mp hle) x
        exact Nat.eq_zero_of_le_zero (by simpa [hk0] using this)
      simp [hk0, hix]
    simpa [Finsupp.prod] using
      (Finset.prod_subset (Finset.subset_univ _) houtside :
        ∏ x ∈ k.support, Nat.choose (k x) (i x) =
          ∏ x ∈ (Finset.univ : Finset σ), Nat.choose (k x) (i x))
  · rw [mvChoose_of_not_le (k := k) (i := i) hle]
    have hnot : ¬ ∀ x, i x ≤ k x := by
      simpa [Finsupp.le_def] using hle
    rcases not_forall.mp hnot with ⟨x, hx⟩
    have hxlt : k x < i x := lt_of_not_ge hx
    have hx0 : Nat.choose (k x) (i x) = 0 := Nat.choose_eq_zero_of_lt hxlt
    have hprod : (∏ y : σ, Nat.choose (k y) (i y)) = 0 := by
      simpa using (Finset.prod_eq_zero (i := x) (by simp) hx0)
    simp [hprod]

private lemma mvChoose_eq_prod_choose_of_support_subset
    (k i : σ →₀ ℕ) (s : Finset σ) (hi : i.support ⊆ s) :
    mvChoose k i = ∏ a : s, (k a).choose (i a) := by
  classical
  by_cases hki : i ≤ k
  · rw [mvChoose_of_le hki]
    have hsupp : i.support ⊆ k.support := by
      intro a ha
      refine Finsupp.mem_support_iff.mpr fun hk0 ↦ ?_
      have : i a ≤ k a := (Finsupp.le_def.mp hki) a
      have hi0 : i a = 0 := Nat.eq_zero_of_le_zero (by simpa [hk0] using this)
      exact (Finsupp.mem_support_iff.mp ha) hi0
    calc
      k.prod (fun a n ↦ n.choose (i a)) = ∏ a ∈ k.support, (k a).choose (i a) := by
        simp [Finsupp.prod]
      _ = ∏ a ∈ k.support ∪ s, (k a).choose (i a) := by
        refine Finset.prod_subset (by
          intro a ha
          exact Finset.mem_union.mpr (Or.inl ha)) ?_
        intro a ha hnotk
        have has : a ∈ s := (Finset.mem_union.mp ha).resolve_left hnotk
        have hnoti : a ∉ i.support := fun h ↦ hnotk (hsupp h)
        have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp hnoti
        simp [hi0]
      _ = ∏ a ∈ s, (k a).choose (i a) := by
        symm
        refine Finset.prod_subset (by
          intro a ha
          exact Finset.mem_union.mpr (Or.inr ha)) ?_
        intro a ha hnots
        have hak : a ∈ k.support := (Finset.mem_union.mp ha).resolve_right hnots
        have hnoti : a ∉ i.support := fun h ↦ hnots (hi h)
        have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp hnoti
        simp [hi0]
      _ = ∏ a : s, (k a).choose (i a) := by
        calc
          ∏ a ∈ s, (k a).choose (i a) = ∏ a ∈ s.attach, (k a).choose (i a) := by
            simpa using (Finset.prod_attach s (fun a ↦ (k a).choose (i a))).symm
          _ = ∏ a : s, (k a).choose (i a) := by
            rw [Finset.univ_eq_attach]
  · rw [mvChoose_of_not_le (k := k) (i := i) hki]
    have hnot : ¬ ∀ a, i a ≤ k a := by
      simpa [Finsupp.le_def] using hki
    rcases not_forall.mp hnot with ⟨a, ha⟩
    have hlt : k a < i a := lt_of_not_ge ha
    have hai : a ∈ i.support := Finsupp.mem_support_iff.mpr
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hlt))
    have has : a ∈ s := hi hai
    refine (Finset.prod_eq_zero (i := ⟨a, has⟩) (by simp) ?_).symm
    simpa using Nat.choose_eq_zero_of_lt hlt

private theorem mvChoose_add (a b i : σ →₀ ℕ) [DecidableEq σ] :
    mvChoose (a + b) i = ∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 := by
  classical
  let τ := {x // x ∈ i.support}
  let ψ : (∀ x : τ, ℕ × ℕ) → (σ →₀ ℕ) × (σ →₀ ℕ) := fun f ↦
    ((Finsupp.equivFunOnFinite.symm fun x : τ ↦ (f x).1).extendDomain,
      (Finsupp.equivFunOnFinite.symm fun x : τ ↦ (f x).2).extendDomain)
  have hψ_mem :
      ∀ f, f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        ψ f ∈ Finset.antidiagonal i := by
    intro f hf
    rw [Finset.mem_antidiagonal]
    ext a
    by_cases ha : a ∈ i.support
    · have hfa : f ⟨a, ha⟩ ∈ Finset.antidiagonal (i a) := (Fintype.mem_piFinset.mp hf) ⟨a, ha⟩
      simpa [ψ, Finsupp.extendDomain_toFun, ha, Finsupp.coe_equivFunOnFinite_symm] using
        (Finset.mem_antidiagonal.mp hfa)
    · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
      simp [ψ, Finsupp.extendDomain_toFun, ha, hi0]
  have hψ_val :
      ∀ f, f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        (∏ x : τ, (a x).choose (f x).1 * (b x).choose (f x).2) =
          mvChoose a (ψ f).1 * mvChoose b (ψ f).2 := by
    intro f hf
    have hsubset₁ :
        (ψ f).1.support ⊆ i.support := by
      intro x hx
      exact (Finsupp.support_extendDomain_subset
        (f := Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).1)) hx
    have hsubset₂ :
        (ψ f).2.support ⊆ i.support := by
      intro x hx
      exact (Finsupp.support_extendDomain_subset
        (f := Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).2)) hx
    have hprod₁ : (∏ x : τ, (a x).choose (f x).1) = mvChoose a (ψ f).1 := by
      rw [mvChoose_eq_prod_choose_of_support_subset (s := i.support) (hi := hsubset₁)]
      symm
      refine Fintype.prod_congr _ _ fun x ↦ ?_
      have hcoe :
          (ψ f).1 ↑x = (f x).1 := by
        change ((Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).1).extendDomain) ↑x = (f x).1
        rw [Finsupp.extendDomain_eq_embDomain_subtype]
        simpa using
          (Finsupp.embDomain_apply_self
            (.subtype fun a : σ ↦ a ∈ i.support)
            (Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).1) x)
      exact congrArg (fun n ↦ (a x).choose n) hcoe
    have hprod₂ : (∏ x : τ, (b x).choose (f x).2) = mvChoose b (ψ f).2 := by
      rw [mvChoose_eq_prod_choose_of_support_subset (s := i.support) (hi := hsubset₂)]
      symm
      refine Fintype.prod_congr _ _ fun x ↦ ?_
      have hcoe :
          (ψ f).2 ↑x = (f x).2 := by
        change ((Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).2).extendDomain) ↑x = (f x).2
        rw [Finsupp.extendDomain_eq_embDomain_subtype]
        simpa using
          (Finsupp.embDomain_apply_self
            (.subtype fun a : σ ↦ a ∈ i.support)
            (Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).2) x)
      exact congrArg (fun n ↦ (b x).choose n) hcoe
    calc
      (∏ x : τ, (a x).choose (f x).1 * (b x).choose (f x).2) =
          (∏ x : τ, (a x).choose (f x).1) * ∏ x : τ, (b x).choose (f x).2 := by
            simpa using
              (Finset.prod_mul_distrib (s := (Finset.univ : Finset τ))
                (f := fun x : τ ↦ (a x).choose (f x).1)
                (g := fun x : τ ↦ (b x).choose (f x).2))
      _ = mvChoose a (ψ f).1 * mvChoose b (ψ f).2 := by rw [hprod₁, hprod₂]
  have hψ_inj :
      ∀ f g,
        f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        g ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        ψ f = ψ g → f = g := by
    intro f g hf hg hfg
    funext x
    apply Prod.ext
    · have h := congrArg (fun p ↦ p.1 x) hfg
      simpa [ψ, Finsupp.extendDomain_toFun, x.prop, Finsupp.coe_equivFunOnFinite_symm] using h
    · have h := congrArg (fun p ↦ p.2 x) hfg
      simpa [ψ, Finsupp.extendDomain_toFun, x.prop, Finsupp.coe_equivFunOnFinite_symm] using h
  have hψ_surj :
      ∀ p, p ∈ Finset.antidiagonal i →
        ∃ f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)), ψ f = p := by
    intro p hp
    let f : ∀ x : τ, ℕ × ℕ := fun x ↦ (p.1 x, p.2 x)
    have hf : f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) := by
      rw [Fintype.mem_piFinset]
      intro x
      have hx : p.1 x + p.2 x = i x := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun q : σ →₀ ℕ => q x) (Finset.mem_antidiagonal.mp hp)
      exact Finset.mem_antidiagonal.mpr (by simpa [f] using hx)
    refine ⟨f, hf, ?_⟩
    apply Prod.ext <;> ext a
    · by_cases ha : a ∈ i.support
      · have hcoe :
            (Finsupp.equivFunOnFinite.symm fun x : τ ↦ p.1 x) ⟨a, ha⟩ = p.1 a := by
          exact congrFun (Finsupp.coe_equivFunOnFinite_symm (f := fun x : τ ↦ p.1 x)) ⟨a, ha⟩
        simpa [ψ, f, Finsupp.extendDomain_toFun, ha, hcoe]
      · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
        have hp0 : p.1 a + p.2 a = 0 := by
          simpa [hi0] using congrArg (fun q : σ →₀ ℕ => q a) (Finset.mem_antidiagonal.mp hp)
        have hp10 : p.1 a = 0 := (Nat.add_eq_zero_iff.mp hp0).1
        simp [ψ, f, Finsupp.extendDomain_toFun, ha, hp10]
    · by_cases ha : a ∈ i.support
      · have hcoe :
            (Finsupp.equivFunOnFinite.symm fun x : τ ↦ p.2 x) ⟨a, ha⟩ = p.2 a := by
          exact congrFun (Finsupp.coe_equivFunOnFinite_symm (f := fun x : τ ↦ p.2 x)) ⟨a, ha⟩
        simpa [ψ, f, Finsupp.extendDomain_toFun, ha, hcoe]
      · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
        have hp0 : p.1 a + p.2 a = 0 := by
          simpa [hi0] using congrArg (fun q : σ →₀ ℕ => q a) (Finset.mem_antidiagonal.mp hp)
        have hp20 : p.2 a = 0 := (Nat.add_eq_zero_iff.mp hp0).2
        simp [ψ, f, Finsupp.extendDomain_toFun, ha, hp20]
  calc
    mvChoose (a + b) i = ∏ x : τ, ((a + b) x).choose (i x) := by
      exact mvChoose_eq_prod_choose_of_support_subset (k := a + b) (i := i)
        (s := i.support) (hi := fun x hx ↦ hx)
    _ = ∏ x : τ, ∑ p ∈ Finset.antidiagonal (i x), (a x).choose p.1 * (b x).choose p.2 := by
      refine Finset.prod_congr rfl fun x _ ↦ ?_
      simpa [Finsupp.add_apply] using (Nat.add_choose_eq (a x) (b x) (i x))
    _ = ∑ f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)),
          ∏ x : τ, (a x).choose (f x).1 * (b x).choose (f x).2 := by
      simpa using
        (Finset.prod_univ_sum
          (t := fun x : τ ↦ Finset.antidiagonal (i x))
          (f := fun x p ↦ (a x).choose p.1 * (b x).choose p.2))
    _ = ∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 := by
      refine Finset.sum_bij (fun f _ ↦ ψ f) hψ_mem
        (fun f hf g hg hfg ↦ hψ_inj f g hf hg hfg)
        (fun p hp ↦ by
          rcases hψ_surj p hp with ⟨f, hf, hfp⟩
          exact ⟨f, hf, hfp⟩)
        hψ_val

/-- The Hasse derivative $\partial^{[i]}$ of multivariate polynomials. -/
def hasseDeriv (i : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  Finsupp.lsum R fun k ↦ (mvChoose k i : R) • MvPolynomial.monomial (k - i)

/-- On a monomial $r X^k$, the Hasse derivative is $\binom{k}{i} r X^{k-i}$. -/
@[simp]
theorem hasseDeriv_monomial (i k : σ →₀ ℕ) (r : R) :
    hasseDeriv i (MvPolynomial.monomial k r) =
      MvPolynomial.monomial (k - i) ((mvChoose k i : R) * r) := by
  classical
  have h : hasseDeriv i (MvPolynomial.monomial k r) =
      ((mvChoose k i : R) • MvPolynomial.monomial (k - i)) r := by
    simpa [hasseDeriv, MvPolynomial.single_eq_monomial] using
      Finsupp.lsum_single (σ := RingHom.id R) (S := R)
        (f := fun k ↦ (mvChoose k i : R) • MvPolynomial.monomial (k - i)) k r
  simpa [LinearMap.smul_apply, MvPolynomial.smul_monomial, smul_eq_mul] using h

lemma hasseDeriv_monomial_eq_prod_choose [Fintype σ] (i k : σ →₀ ℕ) (r : R) :
    hasseDeriv i (MvPolynomial.monomial k r) =
      MvPolynomial.monomial (k - i) (((∏ j : σ, (k j).choose (i j)) : R) * r) := by
  classical
  simp [mvChoose_eq_prod_choose, hasseDeriv_monomial]

/-- The coefficient of $X^m$ in `hasseDeriv i P` is $\binom{m + i}{i}$ times the
coefficient of $X^{m+i}$ in `P`. -/
theorem hasseDeriv_coeff (i : σ →₀ ℕ) (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (hasseDeriv i P) = (mvChoose (m + i) i : R) * coeff (m + i) P := by
  classical
  refine MvPolynomial.induction_on' P (fun k r => ?_) (fun p q hp hq => ?_)
  · by_cases hk : k = m + i
    · subst hk
      have hik : i ≤ m + i := Finsupp.le_def.2 fun x =>
        (Nat.le_add_right (i x) (m x)).trans (le_of_eq (add_comm (i x) (m x)))
      simp [hasseDeriv_monomial, coeff_monomial, mvChoose_of_le hik]
    · have hcoeff : coeff (m + i) (MvPolynomial.monomial k r : MvPolynomial σ R) = 0 := by
        simp [coeff_monomial, hk]
      by_cases hik : i ≤ k
      · have hkm : k - i ≠ m := by
          intro hkm
          have hk' : k - i + i = m + i := by simp [hkm]
          have hk'' : k = m + i := by
            rw [tsub_add_cancel_of_le hik] at hk'
            exact hk'
          exact hk hk''
        simp [hasseDeriv_monomial, coeff_monomial, hkm, hcoeff]
      · simp [hasseDeriv_monomial, mvChoose_of_not_le (k := k) (i := i) hik, hcoeff]
  · simp [hp, hq, coeff_add, mul_add]

/-- The Hasse derivative of order $0$ is the identity. -/
@[simp]
theorem hasseDeriv_zero :
    hasseDeriv (R := R) (0 : σ →₀ ℕ) =
      (LinearMap.id : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) := by
  classical
  refine LinearMap.ext fun p ↦ ?_
  refine MvPolynomial.induction_on' p (fun k r => ?_) (fun p q hp hq => ?_)
  · simp
  · simp [hp, hq]

/-- The composition formula
$\partial^{[i]} \circ \partial^{[j]} = \binom{i + j}{i} \partial^{[i+j]}$. -/
theorem hasseDeriv_comp (i j : σ →₀ ℕ) :
    (hasseDeriv (R := R) i).comp (hasseDeriv j) =
      (mvChoose (i + j) i : R) • hasseDeriv (R := R) (i + j) := by
  classical
  refine LinearMap.ext fun p ↦ ?_
  refine MvPolynomial.induction_on' p (fun k r => ?_) (fun p q hp hq => ?_)
  · have h :
        mvChoose k j * mvChoose (k - j) i =
          mvChoose k (i + j) * mvChoose (i + j) i := by
      have hsymm : mvChoose (i + j) j = mvChoose (i + j) i := by
        simpa [add_comm] using (mvChoose_symm_add (σ := σ) j i)
      calc
        mvChoose k j * mvChoose (k - j) i =
            mvChoose k (i + j) * mvChoose (i + j) j := by
          simpa [add_comm, add_left_comm, add_assoc] using (mvChoose_mul (σ := σ) k j i)
        _ = mvChoose k (i + j) * mvChoose (i + j) i := by simp [hsymm]
    have h' :
        (mvChoose k j : R) * (mvChoose (k - j) i : R) =
          (mvChoose k (i + j) : R) * (mvChoose (i + j) i : R) := by
      have hcast :
          ((mvChoose k j * mvChoose (k - j) i : ℕ) : R) =
            ((mvChoose k (i + j) * mvChoose (i + j) i : ℕ) : R) :=
        congrArg (fun n : ℕ => (n : R)) h
      simpa [Nat.cast_mul] using hcast
    have h'' :
        r * (mvChoose k j : R) * (mvChoose (k - j) i : R) =
          r * (mvChoose k (i + j) : R) * (mvChoose (i + j) i : R) := by
      calc
        r * (mvChoose k j : R) * (mvChoose (k - j) i : R) =
            r * ((mvChoose k j : R) * (mvChoose (k - j) i : R)) := by
          rw [mul_assoc]
        _ = r * ((mvChoose k (i + j) : R) * (mvChoose (i + j) i : R)) := by
          rw [h']
        _ = r * (mvChoose k (i + j) : R) * (mvChoose (i + j) i : R) := by
          rw [mul_assoc]
    simp [LinearMap.comp_apply, LinearMap.smul_apply, hasseDeriv_monomial,
      MvPolynomial.smul_monomial, smul_eq_mul, tsub_tsub, add_comm, mul_comm, h'']
  · have hp' :
        hasseDeriv i (hasseDeriv j p) =
          (mvChoose (i + j) i : R) • hasseDeriv (i + j) p := by
      simpa [LinearMap.comp_apply] using hp
    have hq' :
        hasseDeriv i (hasseDeriv j q) =
          (mvChoose (i + j) i : R) • hasseDeriv (i + j) q := by
      simpa [LinearMap.comp_apply] using hq
    simp [hp', hq']

/-- The multivariate Leibniz rule
$\partial^{[i]} (P Q) = \sum_{p + q = i} \partial^{[p]} P \, \partial^{[q]} Q$. -/
theorem hasseDeriv_mul [DecidableEq σ] (i : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasseDeriv i (P * Q) =
      ∑ p ∈ Finset.antidiagonal i, hasseDeriv p.1 P * hasseDeriv p.2 Q := by
  classical
  refine MvPolynomial.induction_on' P (fun a r ↦ ?_) (fun P₁ P₂ hP₁ hP₂ ↦ ?_)
  · refine MvPolynomial.induction_on' Q (fun b s ↦ ?_) (fun Q₁ Q₂ hQ₁ hQ₂ ↦ ?_)
    · have hsum :
          ∑ p ∈ Finset.antidiagonal i,
              MvPolynomial.monomial (a + b - i)
                ((((mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) * (r * s))) =
            MvPolynomial.monomial (a + b - i)
              ((((∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) *
                (r * s))) := by
        ext m
        by_cases hm : m = a + b - i
        · subst hm
          simp [MvPolynomial.coeff_sum, Nat.cast_sum, Finset.sum_mul]
        · simp [MvPolynomial.coeff_sum, hm, eq_comm]
      have haux :
          ∀ p : (σ →₀ ℕ) × (σ →₀ ℕ), p ∈ Finset.antidiagonal i →
            hasseDeriv p.1 (MvPolynomial.monomial a r) *
                hasseDeriv p.2 (MvPolynomial.monomial b s) =
              MvPolynomial.monomial (a + b - i)
                ((((mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) * (r * s))) := by
        intro p hp
        have hp₁₂ : p.1 + p.2 = i := Finset.mem_antidiagonal.mp hp
        by_cases hpa : p.1 ≤ a
        · by_cases hpb : p.2 ≤ b
          · have hexp :
                a - p.1 + (b - p.2) = a + b - i := by
              calc
                a - p.1 + (b - p.2) = a + (b - p.2) - p.1 := by
                  rw [tsub_add_eq_add_tsub hpa]
                _ = a + b - p.2 - p.1 := by
                  rw [← add_tsub_assoc_of_le hpb]
                _ = a + b - (p.2 + p.1) := by
                  rw [tsub_add_eq_tsub_tsub]
                _ = a + b - (p.1 + p.2) := by simp [add_comm]
                _ = a + b - i := by simp [hp₁₂]
            simp [hasseDeriv_monomial, MvPolynomial.monomial_mul, hexp, mul_assoc,
              mul_left_comm, mul_comm]
          · have hmv : mvChoose b p.2 = 0 := mvChoose_of_not_le (k := b) (i := p.2) hpb
            simp [hasseDeriv_monomial, hmv]
        · have hmv : mvChoose a p.1 = 0 := mvChoose_of_not_le (k := a) (i := p.1) hpa
          simp [hasseDeriv_monomial, hmv]
      calc
        hasseDeriv i (MvPolynomial.monomial a r * MvPolynomial.monomial b s) =
            MvPolynomial.monomial (a + b - i) ((mvChoose (a + b) i : R) * (r * s)) := by
          simp [MvPolynomial.monomial_mul, hasseDeriv_monomial]
        _ =
            MvPolynomial.monomial (a + b - i)
              ((((∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) *
                (r * s))) := by
          congr 2
          rw [mvChoose_add]
        _ =
            ∑ p ∈ Finset.antidiagonal i,
              MvPolynomial.monomial (a + b - i)
                ((((mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) * (r * s))) := by
          simpa using hsum.symm
        _ =
            ∑ p ∈ Finset.antidiagonal i,
              hasseDeriv p.1 (MvPolynomial.monomial a r) *
                hasseDeriv p.2 (MvPolynomial.monomial b s) := by
          refine Finset.sum_congr rfl fun p hp ↦ ?_
          exact (haux p hp).symm
    · rw [mul_add, map_add, hQ₁, hQ₂, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [← mul_add]
      simp [hasseDeriv_monomial]
  · rw [add_mul, map_add, hP₁, hP₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← add_mul]
    simp

/-- The Hasse derivative indexed by `Finsupp.single i 1` is the partial derivative
`pderiv i`. -/
theorem hasseDeriv_single_one (i : σ) :
    hasseDeriv (R := R) (Finsupp.single i 1) = pderiv (R := R) i := by
  classical
  refine LinearMap.ext fun p ↦ ?_
  refine MvPolynomial.induction_on' p (fun k r => ?_) (fun p q hp hq => ?_)
  · rw [hasseDeriv_monomial]
    simp [pderiv_monomial, mvChoose_single, Nat.choose_one_right, mul_comm]
  · simp [hp, hq]

end MvPolynomial
