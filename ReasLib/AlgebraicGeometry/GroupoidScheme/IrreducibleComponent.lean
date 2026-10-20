/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.FieldPoints
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Fiber
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Translation
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents.FixedPoints
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.Topology.IrreducibleComponents.Equiv

/-!
# Irreducible components of groupoid schemes over fields

This module selects the irreducible component through the identity arrow and records its
uniqueness and geometric irreducibility for both field structures induced by source and target.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The irreducible component of the arrow scheme selected by the identity point. -/
def identityIrreducibleComponent {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k)) :
    irreducibleComponents G.R.left :=
  ⟨irreducibleComponent (G.e.left (uIso.inv (IsLocalRing.closedPoint k))),
    irreducibleComponent_mem_irreducibleComponents
      (G.e.left (uIso.inv (IsLocalRing.closedPoint k)))⟩

/-- The identity point belongs to the selected identity component. -/
theorem identity_mem_identityIrreducibleComponent {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k)) :
    G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈
      (identityIrreducibleComponent G uIso : Set G.R.left) :=
  mem_irreducibleComponent

/-- The identity point factors uniquely through the reduced induced closed subscheme attached
to any irreducible component containing it. -/
theorem existsUniqueLiftIdentityPointIntoComponentSubscheme
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    (Z : irreducibleComponents G.R.left)
    (hZ : G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left)) :
    ∃! g : Spec (CommRingCat.of k) ⟶ G.R.left.irreducibleComponentSubscheme Z,
      g ≫ G.R.left.irreducibleComponentSubschemeι Z = uIso.inv ≫ G.e.left := by
  -- Local instance justification (proof-local temporary data): the factorization criterion requires the canonical reducedness of the field spectrum only within this proof.
  letI : IsReduced (Spec (CommRingCat.of k)) := inferInstance
  rw [Scheme.IdealSheafData.existsUnique_lift_iff_range_subset
    (Z := Scheme.IdealSheafData.vanishingIdeal (G.R.left.irreducibleComponentClosed Z))
    (f := uIso.inv ≫ G.e.left)]
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  simpa [hx, Scheme.irreducibleComponentSubscheme, Scheme.irreducibleComponentSubschemeι,
    Scheme.mem_irreducibleComponentClosed] using hZ

/-- The two component-subscheme projections satisfy the source-target compatibility needed for
the ambient composition-domain pullback. -/
theorem componentPullbackToCompositionDomain_condition
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (Z I : irreducibleComponents G.R.left) :
    (Limits.pullback.fst (C := Scheme.{u})
      (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
      (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left) =
      (Limits.pullback.snd (C := Scheme.{u})
      (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
      (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) := by
  simpa [Category.assoc] using
    (show
      Limits.pullback.fst (C := Scheme.{u})
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left) =
      Limits.pullback.snd (C := Scheme.{u})
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) from
      Limits.pullback.condition
        (f := G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
        (g := G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left))

/-- The pullback of two irreducible-component subschemes maps canonically to the composition
domain `R ×_{s, U, t} R`. -/
noncomputable def componentPullbackToCompositionDomain
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (Z I : irreducibleComponents G.R.left) :
    Limits.pullback (C := Scheme.{u})
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ⟶
      Limits.pullback (C := Scheme.{u}) G.s.left G.t.left :=
  Limits.pullback.lift
    (Limits.pullback.fst (C := Scheme.{u})
      (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
      (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        G.R.left.irreducibleComponentSubschemeι Z)
    (Limits.pullback.snd (C := Scheme.{u})
      (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
      (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        G.R.left.irreducibleComponentSubschemeι I)
    (componentPullbackToCompositionDomain_condition G Z I)

/-- The first projection of the component-pullback map is the inclusion of the first component
subscheme. -/
theorem componentPullbackToCompositionDomain_fst
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (Z I : irreducibleComponents G.R.left) :
    componentPullbackToCompositionDomain G Z I ≫
        Limits.pullback.fst (C := Scheme.{u}) G.s.left G.t.left =
      Limits.pullback.fst (C := Scheme.{u})
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        G.R.left.irreducibleComponentSubschemeι Z := by
  simpa [componentPullbackToCompositionDomain, Category.assoc] using
    Limits.pullback.lift_fst
      (Limits.pullback.fst (C := Scheme.{u})
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
          G.R.left.irreducibleComponentSubschemeι Z)
      (Limits.pullback.snd (C := Scheme.{u})
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
          G.R.left.irreducibleComponentSubschemeι I)
      (componentPullbackToCompositionDomain_condition G Z I)

/-- The second projection of the component-pullback map is the inclusion of the second component
subscheme. -/
theorem componentPullbackToCompositionDomain_snd
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (Z I : irreducibleComponents G.R.left) :
    componentPullbackToCompositionDomain G Z I ≫
        Limits.pullback.snd (C := Scheme.{u}) G.s.left G.t.left =
      Limits.pullback.snd (C := Scheme.{u})
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
        G.R.left.irreducibleComponentSubschemeι I := by
  simpa [componentPullbackToCompositionDomain, Category.assoc] using
    Limits.pullback.lift_snd
      (Limits.pullback.fst (C := Scheme.{u})
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
          G.R.left.irreducibleComponentSubschemeι Z)
      (Limits.pullback.snd (C := Scheme.{u})
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left) ≫
          G.R.left.irreducibleComponentSubschemeι I)
      (componentPullbackToCompositionDomain_condition G Z I)

/-- The identity arrow of a restricted groupoid scheme maps to the original identity arrow, so it
lies over every downstairs irreducible component containing the identity point. -/
theorem restrictedIdentity_mem_preimage_component
    {S : Scheme.{u}} (G : GroupoidScheme S) {k K : Type u} [Field k] [Field K]
    (uIso : G.U.left ≅ Spec (CommRingCat.of k)) [Algebra k K]
    (Z : irreducibleComponents G.R.left)
    (hZ : G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left)) :
    let g := G.fieldRestriction uIso.symm (algebraMap k K)
    let G' := G.pullback g
    let φ := G.pullbackHom g
    φ.arrow.left (G'.e.left (IsLocalRing.closedPoint K)) ∈ (Z : Set G.R.left) := by
  dsimp
  rw [restrictionArrow_unit]
  have hClosedPoint :
      Spec.map (CommRingCat.ofHom (algebraMap k K)) (IsLocalRing.closedPoint K) =
        IsLocalRing.closedPoint k := by
    exact Subsingleton.elim _ _
  have hFieldRestrictionPoint :
      G.fieldRestrictionMap uIso.symm (algebraMap k K) (IsLocalRing.closedPoint K) =
        uIso.inv (IsLocalRing.closedPoint k) := by
    change (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ uIso.inv)
        (IsLocalRing.closedPoint K) = uIso.inv (IsLocalRing.closedPoint k)
    simp [hClosedPoint]
  change G.e.left (G.fieldRestrictionMap uIso.symm (algebraMap k K)
      (IsLocalRing.closedPoint K)) ∈ (Z : Set G.R.left)
  rw [hFieldRestrictionPoint]
  exact hZ

/-- The field-based pullback of two component subschemes satisfies the composition-domain
compatibility over `G.U.left` after cancelling the chosen base-field identification. -/
theorem componentPullbackOverField_condition
    {S : Scheme.{u}} (G : GroupoidScheme S) {K : Type u} [Field K]
    (uIso : G.U.left ≅ Spec (CommRingCat.of K))
    (Z I : irreducibleComponents G.R.left) :
    let zOver := G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom
    let iOver := G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom
    Limits.pullback.fst zOver iOver ≫ G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left =
      Limits.pullback.snd zOver iOver ≫ G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left := by
  dsimp
  apply (cancel_mono uIso.hom).1
  simpa [Category.assoc] using
    (show
      Limits.pullback.fst
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom) =
      Limits.pullback.snd
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) from
      Limits.pullback.condition
        (f := G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
        (g := G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom))

/-- The field-based pullback of two component subschemes maps canonically to the groupoid
composition domain `R ×_{s, U, t} R`. -/
noncomputable def componentPullbackOverFieldToCompositionDomain
    {S : Scheme.{u}} (G : GroupoidScheme S) {K : Type u} [Field K]
    (uIso : G.U.left ≅ Spec (CommRingCat.of K))
    (Z I : irreducibleComponents G.R.left) :
    Limits.pullback
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ⟶
      Limits.pullback (C := Scheme.{u}) G.s.left G.t.left :=
  Limits.pullback.lift
    (Limits.pullback.fst
      (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
      (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
        G.R.left.irreducibleComponentSubschemeι Z)
    (Limits.pullback.snd
      (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
      (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
        G.R.left.irreducibleComponentSubschemeι I)
    (componentPullbackOverField_condition G uIso Z I)

/-- The first projection of the field-based pullback comparison is the inclusion of `Z` into the
ambient composition domain. -/
theorem componentPullbackOverFieldToCompositionDomain_fst
    {S : Scheme.{u}} (G : GroupoidScheme S) {K : Type u} [Field K]
    (uIso : G.U.left ≅ Spec (CommRingCat.of K))
    (Z I : irreducibleComponents G.R.left) :
    componentPullbackOverFieldToCompositionDomain G uIso Z I ≫
        Limits.pullback.fst (C := Scheme.{u}) G.s.left G.t.left =
      Limits.pullback.fst
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
        G.R.left.irreducibleComponentSubschemeι Z := by
  simpa [componentPullbackOverFieldToCompositionDomain, Category.assoc] using
    Limits.pullback.lift_fst
      (Limits.pullback.fst
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
          G.R.left.irreducibleComponentSubschemeι Z)
      (Limits.pullback.snd
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
          G.R.left.irreducibleComponentSubschemeι I)
      (componentPullbackOverField_condition G uIso Z I)

/-- The second projection of the field-based pullback comparison is the inclusion of `I` into the
ambient composition domain. -/
theorem componentPullbackOverFieldToCompositionDomain_snd
    {S : Scheme.{u}} (G : GroupoidScheme S) {K : Type u} [Field K]
    (uIso : G.U.left ≅ Spec (CommRingCat.of K))
    (Z I : irreducibleComponents G.R.left) :
    componentPullbackOverFieldToCompositionDomain G uIso Z I ≫
        Limits.pullback.snd (C := Scheme.{u}) G.s.left G.t.left =
      Limits.pullback.snd
          (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
          (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
        G.R.left.irreducibleComponentSubschemeι I := by
  simpa [componentPullbackOverFieldToCompositionDomain, Category.assoc] using
    Limits.pullback.lift_snd
      (Limits.pullback.fst
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
          G.R.left.irreducibleComponentSubschemeι Z)
      (Limits.pullback.snd
        (G.R.left.irreducibleComponentSubschemeι Z ≫ G.s.left ≫ uIso.hom)
        (G.R.left.irreducibleComponentSubschemeι I ≫ G.t.left ≫ uIso.hom) ≫
          G.R.left.irreducibleComponentSubschemeι I)
      (componentPullbackOverField_condition G uIso Z I)

/-- Exactly one irreducible component of the arrow scheme contains the identity point. -/
theorem existsUniqueIrreducibleComponent_throughIdentity
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (uIso : G.U.left ≅ Spec (CommRingCat.of k)) :
    ∃! Z : irreducibleComponents G.R.left,
      G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left) := by
  refine ⟨identityIrreducibleComponent G uIso,
    identity_mem_identityIrreducibleComponent G uIso, ?_⟩
  intro Z hZ
  let K := AlgebraicClosure k
  let g := G.fieldRestriction uIso.symm (algebraMap k K)
  let G' := G.pullback g
  let φ := G.pullbackHom g
  have hZpre :
      φ.arrow.left (G'.e.left (IsLocalRing.closedPoint K)) ∈ (Z : Set G.R.left) :=
    restrictedIdentity_mem_preimage_component (G := G) (uIso := uIso) (K := K) Z hZ
  have hIpre :
      φ.arrow.left (G'.e.left (IsLocalRing.closedPoint K)) ∈
        (identityIrreducibleComponent G uIso : Set G.R.left) :=
    restrictedIdentity_mem_preimage_component (G := G) (uIso := uIso) (K := K)
      (identityIrreducibleComponent G uIso)
      (identity_mem_identityIrreducibleComponent G uIso)
  sorry

/-- Any irreducible component containing the identity point is the selected identity component. -/
theorem eq_identityIrreducibleComponent_of_mem {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    (Z : irreducibleComponents G.R.left)
    (hZ : G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left)) :
    Z = identityIrreducibleComponent G uIso := by
  rcases existsUniqueIrreducibleComponent_throughIdentity G uIso with ⟨Z₀, hZ₀, huniq⟩
  exact (huniq Z hZ).trans
    (huniq (identityIrreducibleComponent G uIso)
      (identity_mem_identityIrreducibleComponent G uIso)).symm

/-- Any irreducible component of the arrow scheme containing the identity point is geometrically
irreducible over the field through the source map. -/
theorem geometricallyIrreducible_identityIrreducibleComponentSource
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    (Z : irreducibleComponents G.R.left)
    (hZ : G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left)) :
    GeometricallyIrreducible
      (irreducibleComponentSubschemeι G.R.left Z ≫ G.s.left ≫ uIso.hom) := by
  rw [eq_identityIrreducibleComponent_of_mem G uIso Z hZ]
  sorry

/-- Any irreducible component of the arrow scheme containing the identity point is geometrically
irreducible over the field through the target map. -/
theorem geometricallyIrreducible_identityIrreducibleComponentTarget
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    (Z : irreducibleComponents G.R.left)
    (hZ : G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left)) :
    GeometricallyIrreducible
      (irreducibleComponentSubschemeι G.R.left Z ≫ G.t.left ≫ uIso.hom) := by
  rw [eq_identityIrreducibleComponent_of_mem G uIso Z hZ]
  sorry

end AlgebraicGeometry.GroupoidScheme
