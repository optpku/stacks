/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducible closed subsets through a localized prime

This leaf packages the canonical order isomorphisms behind the two
correspondences of Lemma 10.26.3. The data is built from Mathlib's spectrum,
irreducible-closed, and minimal-prime order isomorphisms; only the order-law
transport and component correspondence are proved below.

@stack 00ET
-/

@[expose] public section

noncomputable section

open TopologicalSpace

universe u

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

namespace LocalizationIrreducible

/-- Restrict an order isomorphism to predicates that it identifies. -/
theorem restrictOrderIso_map_rel_iff
    {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ x, P x ↔ Q (e x)) (x y : {x // P x}) :
    (e.toEquiv.subtypeEquiv h x : {y // Q y}) ≤ e.toEquiv.subtypeEquiv h y ↔ x ≤ y := by
  change e x.1 ≤ e y.1 ↔ x.1 ≤ y.1
  exact e.map_rel_iff

/-- Restrict an order isomorphism to predicates that it identifies. -/
def restrictOrderIso
    {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ x, P x ↔ Q (e x)) : {x // P x} ≃o {y // Q y} where
  toEquiv := e.toEquiv.subtypeEquiv h
  map_rel_iff' := fun {x y} ↦ restrictOrderIso_map_rel_iff e P Q h x y

/-- Exchange the order of two nested subtype predicates. -/
def swapSubtypeTo
    {α : Type*} (P Q : α → Prop)
    (x : {x : {a // P a} // Q x.1}) : {x : {a // Q a} // P x.1} :=
  ⟨⟨x.1.1, x.2⟩, x.1.2⟩

/-- Exchange two nested subtype predicates in the reverse direction. -/
def swapSubtypeFrom
    {α : Type*} (P Q : α → Prop)
    (x : {x : {a // Q a} // P x.1}) : {x : {a // P a} // Q x.1} :=
  ⟨⟨x.1.1, x.2⟩, x.1.2⟩

/-- Swapping nested subtype predicates and swapping back is the identity. -/
theorem swapSubtype_leftInverse
    {α : Type*} (P Q : α → Prop) :
    Function.LeftInverse (swapSubtypeFrom P Q) (swapSubtypeTo P Q) := by
  intro x
  rfl

/-- Swapping nested subtype predicates is surjective with the evident inverse. -/
theorem swapSubtype_rightInverse
    {α : Type*} (P Q : α → Prop) :
    Function.RightInverse (swapSubtypeFrom P Q) (swapSubtypeTo P Q) := by
  intro x
  rfl

/-- Swapping nested subtype predicates preserves the inherited order. -/
theorem swapSubtype_map_rel_iff
    {α : Type*} [Preorder α] (P Q : α → Prop)
    (x y : {x : {a // P a} // Q x.1}) :
    swapSubtypeTo P Q x ≤ swapSubtypeTo P Q y ↔ x ≤ y := Iff.rfl

/-- The order isomorphism exchanging two nested subtype predicates. -/
def swapSubtypeOrderIso
    {α : Type*} [Preorder α] (P Q : α → Prop) :
    {x : {a // P a} // Q x.1} ≃o {x : {a // Q a} // P x.1} where
  toFun := swapSubtypeTo P Q
  invFun := swapSubtypeFrom P Q
  left_inv := swapSubtype_leftInverse P Q
  right_inv := swapSubtype_rightInverse P Q
  map_rel_iff' := fun {x y} ↦ swapSubtype_map_rel_iff P Q x y

end LocalizationIrreducible

/-- Under the point/irreducible-closed correspondence, containment is the
specialization order. -/
@[stacks 00ET "point and irreducible-closed incidence"]
theorem mem_pointsEquivIrreducibleCloseds_iff_le (p q : PrimeSpectrum R) :
    p ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) ↔ q ≤ p := by
  change p ∈ closure ({q} : Set (PrimeSpectrum R)) ↔ q ≤ p
  rw [PrimeSpectrum.closure_singleton]
  rfl

/-- Lemma 10.26.3 (1): primes of `R_p` are canonically order-isomorphic to
irreducible closed subsets of `Spec R` containing `p`. -/
@[stacks 00ET "(1) irreducible closed subsets"]
noncomputable def localizationAtPrimeIrreducibleCloseds
    (p : PrimeSpectrum R) :
    PrimeSpectrum (Localization.AtPrime p.asIdeal) ≃o
      ({Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R))})ᵒᵈ :=
  (IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.asIdeal) p.asIdeal).trans
    (LocalizationIrreducible.restrictOrderIso
      (PrimeSpectrum.pointsEquivIrreducibleCloseds R)
      (fun q : PrimeSpectrum R ↦ q ≤ p)
      (fun Z : (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ ↦
        p ∈ (show IrreducibleCloseds (PrimeSpectrum R) from Z : Set (PrimeSpectrum R)))
      (fun q ↦ (mem_pointsEquivIrreducibleCloseds_iff_le p q).symm))

namespace LocalizationIrreducible

/-- View an irreducible component as an irreducible closed subset carrying
its component-membership proof. -/
noncomputable def irreducibleComponentToClosed
    {X : Type*} [TopologicalSpace X] (Z : irreducibleComponents X) :
    {W : IrreducibleCloseds X // (W : Set X) ∈ irreducibleComponents X} :=
  ⟨⟨Z.1, Z.2.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩, Z.2⟩

/-- Forget the bundled irreducible-closed structure on an irreducible
component. -/
def irreducibleClosedToComponent
    {X : Type*} [TopologicalSpace X]
    (Z : {W : IrreducibleCloseds X // (W : Set X) ∈ irreducibleComponents X}) :
    irreducibleComponents X :=
  ⟨(Z.1 : Set X), Z.2⟩

/-- The two component presentations are inverse in the forward direction. -/
theorem irreducibleComponentToClosed_leftInverse
    {X : Type*} [TopologicalSpace X] :
    Function.LeftInverse (@irreducibleClosedToComponent X _)
      (@irreducibleComponentToClosed X _) := by
  intro Z
  rfl

/-- The two component presentations are inverse in the reverse direction. -/
theorem irreducibleComponentToClosed_rightInverse
    {X : Type*} [TopologicalSpace X] :
    Function.RightInverse (@irreducibleClosedToComponent X _)
      (@irreducibleComponentToClosed X _) := by
  intro Z
  rfl

/-- The two component presentations carry the same inclusion order. -/
theorem irreducibleComponentToClosed_map_rel_iff
    {X : Type*} [TopologicalSpace X] (Z W : irreducibleComponents X) :
    irreducibleComponentToClosed Z ≤ irreducibleComponentToClosed W ↔ Z ≤ W := Iff.rfl

/-- Irreducible components and irreducible closed subsets maximal among all
irreducible closed subsets are the same ordered data. -/
noncomputable def irreducibleComponentsOrderIsoIrreducibleCloseds
    (X : Type*) [TopologicalSpace X] :
    irreducibleComponents X ≃o
      {Z : IrreducibleCloseds X // (Z : Set X) ∈ irreducibleComponents X} where
  toFun := irreducibleComponentToClosed
  invFun := irreducibleClosedToComponent
  left_inv := irreducibleComponentToClosed_leftInverse
  right_inv := irreducibleComponentToClosed_rightInverse
  map_rel_iff' := fun {Z W} ↦ irreducibleComponentToClosed_map_rel_iff Z W

end LocalizationIrreducible

/-- The irreducible-closed correspondence induced by localization at `p`. -/
noncomputable def localizationAtPrimeIrreducibleClosedsOrderIso
    (p : PrimeSpectrum R) :
    IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ≃o
      {Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R))} :=
  ((PrimeSpectrum.pointsEquivIrreducibleCloseds
      (Localization.AtPrime p.asIdeal)).symm.trans
    (localizationAtPrimeIrreducibleCloseds p)).dual

/-- Localization at `p` identifies local irreducible components with global
irreducible components containing `p`. -/
theorem localizationAtPrimeIrreducibleClosedsOrderIso_mem_component_iff
    (p : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal))) :
    (Z : Set (PrimeSpectrum (Localization.AtPrime p.asIdeal))) ∈
        irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ↔
      ((localizationAtPrimeIrreducibleClosedsOrderIso p Z).1 :
        Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) := by
  have hmax {X : Type u} [TopologicalSpace X] (W : IrreducibleCloseds X) :
      (W : Set X) ∈ irreducibleComponents X ↔ IsMax W := by
    rw [irreducibleComponents_eq_maximals_closed]
    constructor
    · intro h V hWV
      exact h.2 ⟨V.isClosed, V.isIrreducible⟩ hWV
    · intro h
      refine ⟨⟨W.isClosed, W.isIrreducible⟩, ?_⟩
      intro V hV hWV
      exact h (b := ⟨V, hV.2, hV.1⟩) hWV
  let e := localizationAtPrimeIrreducibleClosedsOrderIso p
  rw [hmax, hmax, ← e.isMax_apply]
  change IsMax (e Z) ↔ IsMax (e Z).1
  constructor
  · intro h W hZW
    exact h (b := ⟨W, hZW (e Z).2⟩) hZW
  · intro h W hZW
    exact h (b := W.1) hZW

/-- The component/irreducible-closed order isomorphism preserves membership
of a point. -/
theorem irreducibleComponentsOrderIso_mem_iff
    (p : PrimeSpectrum R) (Z : irreducibleComponents (PrimeSpectrum R)) :
    p ∈ (Z.1 : Set (PrimeSpectrum R)) ↔
      p ∈ ((LocalizationIrreducible.irreducibleComponentsOrderIsoIrreducibleCloseds
        (PrimeSpectrum R) Z).1 : Set (PrimeSpectrum R)) := Iff.rfl

/-- Lemma 10.26.3 (2): minimal primes of `R_p` are canonically
order-isomorphic to irreducible components of `Spec R` containing `p`. -/
@[stacks 00ET "(2) irreducible components"]
noncomputable def localizationAtPrimeIrreducibleComponents
    (p : PrimeSpectrum R) :
    minimalPrimes (Localization.AtPrime p.asIdeal) ≃o
      ({Z : irreducibleComponents (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R))})ᵒᵈ :=
  let localComponents :
      irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ≃o
        {Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) //
          (Z : Set (PrimeSpectrum (Localization.AtPrime p.asIdeal))) ∈
            irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal))} :=
    LocalizationIrreducible.irreducibleComponentsOrderIsoIrreducibleCloseds _
  let localizedComponents :
      {Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) //
          (Z : Set (PrimeSpectrum (Localization.AtPrime p.asIdeal))) ∈
            irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal))} ≃o
        {Z : {W : IrreducibleCloseds (PrimeSpectrum R) //
            p ∈ (W : Set (PrimeSpectrum R))} //
          (Z.1 : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R)} :=
    LocalizationIrreducible.restrictOrderIso
      (localizationAtPrimeIrreducibleClosedsOrderIso p)
      (fun Z ↦ (Z : Set (PrimeSpectrum (Localization.AtPrime p.asIdeal))) ∈
        irreducibleComponents (PrimeSpectrum (Localization.AtPrime p.asIdeal)))
      (fun Z ↦ (Z.1 : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R))
      (localizationAtPrimeIrreducibleClosedsOrderIso_mem_component_iff p)
  let globalComponents :
      {Z : irreducibleComponents (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R))} ≃o
        {Z : {W : IrreducibleCloseds (PrimeSpectrum R) //
            (W : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R)} //
          p ∈ (Z.1 : Set (PrimeSpectrum R))} :=
    LocalizationIrreducible.restrictOrderIso
      (LocalizationIrreducible.irreducibleComponentsOrderIsoIrreducibleCloseds
        (PrimeSpectrum R))
      (fun Z ↦ p ∈ (Z.1 : Set (PrimeSpectrum R)))
      (fun Z ↦ p ∈ (Z.1 : Set (PrimeSpectrum R)))
      (irreducibleComponentsOrderIso_mem_iff p)
  let reorderedComponents :
      {Z : {W : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (W : Set (PrimeSpectrum R))} //
        (Z.1 : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R)} ≃o
        {Z : {W : IrreducibleCloseds (PrimeSpectrum R) //
            (W : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R)} //
          p ∈ (Z.1 : Set (PrimeSpectrum R))} :=
    LocalizationIrreducible.swapSubtypeOrderIso
      (fun W : IrreducibleCloseds (PrimeSpectrum R) ↦
        p ∈ (W : Set (PrimeSpectrum R)))
      (fun W ↦ (W : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R))
  (minimalPrimes.equivIrreducibleComponents
      (Localization.AtPrime p.asIdeal)).trans
    (localComponents.trans
      (localizedComponents.trans (reorderedComponents.trans globalComponents.symm))).dual

end PrimeSpectrum
