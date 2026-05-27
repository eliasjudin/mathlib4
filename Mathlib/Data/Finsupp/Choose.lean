/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
module

public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Order

import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Coordinatewise binomial coefficients

This file defines `Finsupp.choose`, the coordinatewise binomial coefficient
$\binom{k}{i}=\prod_j \binom{k_j}{i_j}$ for finitely supported `k, i : σ →₀ ℕ`, and proves
basic identities including the finitely supported Vandermonde identity.

## Main declarations

* `Finsupp.choose`
* `Finsupp.choose_add`

## Tags

finitely supported function, binomial coefficient
-/

@[expose] public section

namespace Finsupp

open scoped BigOperators

variable {σ : Type*}

/-! ### Coordinatewise binomial coefficients -/

/-- The coordinatewise binomial coefficient $\binom{k}{i}$. -/
def choose (k i : σ →₀ ℕ) : ℕ :=
  i.prod (fun j m ↦ (k j).choose m)

lemma choose_of_le {k i : σ →₀ ℕ} (h : i ≤ k) :
    choose k i = k.prod (fun j n ↦ n.choose (i j)) := by
  classical
  simp only [choose, Finsupp.prod]
  refine Finset.prod_subset (Finsupp.support_mono h) fun j _ hj ↦ ?_
  rw [Finsupp.notMem_support_iff.mp hj, Nat.choose_zero_right]

lemma choose_of_not_le {k i : σ →₀ ℕ} (h : ¬ i ≤ k) : choose k i = 0 := by
  classical
  simp only [Finsupp.le_def, not_forall] at h
  obtain ⟨x, hx⟩ := h
  simp only [choose, Finsupp.prod]
  have hxlt : k x < i x := lt_of_not_ge hx
  refine Finset.prod_eq_zero (i := x) ?_ (Nat.choose_eq_zero_of_lt hxlt)
  · exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hxlt))

@[simp]
lemma choose_zero (k : σ →₀ ℕ) : choose k 0 = 1 := by
  simp [choose]

@[simp]
lemma choose_self (k : σ →₀ ℕ) : choose k k = 1 := by
  simp [choose, Finsupp.prod]

/-- For a single-coordinate multi-index, `choose` is the usual binomial coefficient. -/
@[simp]
lemma choose_single (k : σ →₀ ℕ) (i : σ) (j : ℕ) :
    choose k (Finsupp.single i j) = Nat.choose (k i) j := by
  classical
  by_cases hj : j = 0
  · simp [hj, choose]
  · simp [choose, Finsupp.prod, hj]

/-- Over a finite index type, $\binom{k}{i} = \prod_{j : \sigma} \binom{k_j}{i_j}$. -/
lemma choose_eq_prod_choose [Fintype σ] (k i : σ →₀ ℕ) :
    choose k i = ∏ j : σ, (k j).choose (i j) := by
  classical
  by_cases hle : i ≤ k
  · rw [choose_of_le (k := k) (i := i) hle]
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
  · rw [choose_of_not_le (k := k) (i := i) hle]
    have hnot : ¬ ∀ x, i x ≤ k x := by
      simpa [Finsupp.le_def] using hle
    rcases not_forall.mp hnot with ⟨x, hx⟩
    have hxlt : k x < i x := lt_of_not_ge hx
    have hx0 : Nat.choose (k x) (i x) = 0 := Nat.choose_eq_zero_of_lt hxlt
    have hprod : (∏ y : σ, Nat.choose (k y) (i y)) = 0 := by
      simpa using (Finset.prod_eq_zero (i := x) (by simp) hx0)
    simp [hprod]

private lemma choose_eq_prod_choose_of_support_subset
    (k i : σ →₀ ℕ) (s : Finset σ) (hi : i.support ⊆ s) :
    choose k i = ∏ a : s, (k a).choose (i a) := by
  classical
  by_cases hki : i ≤ k
  · rw [choose_of_le hki]
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
  · rw [choose_of_not_le (k := k) (i := i) hki]
    have hnot : ¬ ∀ a, i a ≤ k a := by
      simpa [Finsupp.le_def] using hki
    rcases not_forall.mp hnot with ⟨a, ha⟩
    have hlt : k a < i a := lt_of_not_ge ha
    have hai : a ∈ i.support := Finsupp.mem_support_iff.mpr
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hlt))
    have has : a ∈ s := hi hai
    refine (Finset.prod_eq_zero (i := ⟨a, has⟩) (by simp) ?_).symm
    simpa using Nat.choose_eq_zero_of_lt hlt

theorem choose_add (a b i : σ →₀ ℕ) [DecidableEq σ] :
    choose (a + b) i = ∑ p ∈ Finset.antidiagonal i, choose a p.1 * choose b p.2 := by
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
    · have hfa : f ⟨a, ha⟩ ∈ Finset.antidiagonal (i a) :=
        (Fintype.mem_piFinset.mp hf) ⟨a, ha⟩
      simpa [ψ, Finsupp.extendDomain_apply, ha, Finsupp.coe_equivFunOnFinite_symm] using
        (Finset.mem_antidiagonal.mp hfa)
    · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
      simp [ψ, Finsupp.extendDomain_apply, ha, hi0]
  have hψ_val :
      ∀ f, f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        (∏ x : τ, (a x).choose (f x).1 * (b x).choose (f x).2) =
          choose a (ψ f).1 * choose b (ψ f).2 := by
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
    have hprod₁ : (∏ x : τ, (a x).choose (f x).1) = choose a (ψ f).1 := by
      rw [choose_eq_prod_choose_of_support_subset (s := i.support) (hi := hsubset₁)]
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
    have hprod₂ : (∏ x : τ, (b x).choose (f x).2) = choose b (ψ f).2 := by
      rw [choose_eq_prod_choose_of_support_subset (s := i.support) (hi := hsubset₂)]
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
      _ = choose a (ψ f).1 * choose b (ψ f).2 := by rw [hprod₁, hprod₂]
  have hψ_inj :
      ∀ f g,
        f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        g ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        ψ f = ψ g → f = g := by
    intro f g hf hg hfg
    funext x
    apply Prod.ext
    · have h := congrArg (fun p ↦ p.1 x) hfg
      simpa [ψ, Finsupp.extendDomain_apply, x.prop, Finsupp.coe_equivFunOnFinite_symm] using h
    · have h := congrArg (fun p ↦ p.2 x) hfg
      simpa [ψ, Finsupp.extendDomain_apply, x.prop, Finsupp.coe_equivFunOnFinite_symm] using h
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
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hcoe]
      · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
        have hp0 : p.1 a + p.2 a = 0 := by
          simpa [hi0] using congrArg (fun q : σ →₀ ℕ => q a) (Finset.mem_antidiagonal.mp hp)
        have hp10 : p.1 a = 0 := (Nat.add_eq_zero_iff.mp hp0).1
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hp10]
    · by_cases ha : a ∈ i.support
      · have hcoe :
            (Finsupp.equivFunOnFinite.symm fun x : τ ↦ p.2 x) ⟨a, ha⟩ = p.2 a := by
          exact congrFun (Finsupp.coe_equivFunOnFinite_symm (f := fun x : τ ↦ p.2 x)) ⟨a, ha⟩
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hcoe]
      · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
        have hp0 : p.1 a + p.2 a = 0 := by
          simpa [hi0] using congrArg (fun q : σ →₀ ℕ => q a) (Finset.mem_antidiagonal.mp hp)
        have hp20 : p.2 a = 0 := (Nat.add_eq_zero_iff.mp hp0).2
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hp20]
  calc
    choose (a + b) i = ∏ x : τ, ((a + b) x).choose (i x) := by
      exact choose_eq_prod_choose_of_support_subset (k := a + b) (i := i)
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
    _ = ∑ p ∈ Finset.antidiagonal i, choose a p.1 * choose b p.2 := by
      refine Finset.sum_bij (fun f _ ↦ ψ f) hψ_mem
        (fun f hf g hg hfg ↦ hψ_inj f g hf hg hfg)
        (fun p hp ↦ by
          rcases hψ_surj p hp with ⟨f, hf, hfp⟩
          exact ⟨f, hf, hfp⟩)
        hψ_val

end Finsupp
