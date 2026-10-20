/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents.FixedPoints
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

noncomputable section

/-- The irreducible component of a group scheme selected by its identity point. -/
def identityIrreducibleComponent (G : SchemeOverField k) [GrpObj G] :
    irreducibleComponents G.left :=
  ⟨irreducibleComponent (η[G].left (IsLocalRing.closedPoint k)),
    irreducibleComponent_mem_irreducibleComponents (η[G].left (IsLocalRing.closedPoint k))⟩

/-- The identity point belongs to the selected irreducible component. -/
theorem identity_mem_identityIrreducibleComponent
    (G : SchemeOverField k) [GrpObj G] :
    η[G].left (IsLocalRing.closedPoint k) ∈ (identityIrreducibleComponent G : Set G.left) :=
  mem_irreducibleComponent

/-- A component containing the identity point receives a unique lift of that point through its
reduced induced closed subscheme. -/
theorem existsUnique_lift_identityPoint_into_componentSubscheme
    (G : SchemeOverField k) [GrpObj G] (Z : irreducibleComponents G.left)
    (hZ : η[G].left (IsLocalRing.closedPoint k) ∈ (Z : Set G.left)) :
    ∃! g : Over.left (𝟙_ (SchemeOverField k)) ⟶ G.left.irreducibleComponentSubscheme Z,
      g ≫ G.left.irreducibleComponentSubschemeι Z = η[G].left := by
  -- Local instance justification (defeq pin): the terminal slice source is definitionally `Spec (CommRingCat.of k)`, whose reduced instance is needed below.
  letI : IsReduced (Over.left (𝟙_ (SchemeOverField k))) := by
    change IsReduced (Spec (CommRingCat.of k))
    infer_instance
  rw [Scheme.IdealSheafData.existsUnique_lift_iff_range_subset
    (Z := Scheme.IdealSheafData.vanishingIdeal (G.left.irreducibleComponentClosed Z))
    (f := η[G].left)]
  intro y hy
  rcases hy with ⟨x, rfl⟩
  -- The field spectrum has a unique point, so every point of the identity section is the
  -- distinguished identity point already known to lie in `Z`.
  change Spec (CommRingCat.of k) at x
  have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  simpa [hx, Scheme.irreducibleComponentSubscheme, Scheme.irreducibleComponentSubschemeι,
    Scheme.mem_irreducibleComponentClosed] using hZ

/-- Over an algebraically closed field, any irreducible component containing the identity point
coincides with the selected identity component. -/
theorem eqIdentityIrreducibleComponentOfMem_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : SchemeOverField K) [GrpObj G] {Z : irreducibleComponents G.left}
    (hZ : η[G].left (IsLocalRing.closedPoint K) ∈ (Z : Set G.left)) :
    Z = identityIrreducibleComponent G := by
  let I : irreducibleComponents G.left := identityIrreducibleComponent G
  let ZOver : SchemeOverField K := Over.mk (G.left.irreducibleComponentSubschemeι Z ≫ G.hom)
  let IOver : SchemeOverField K := Over.mk (G.left.irreducibleComponentSubschemeι I ≫ G.hom)
  let zInclusion : ZOver ⟶ G := Over.homMk (G.left.irreducibleComponentSubschemeι Z)
  let iInclusion : IOver ⟶ G := Over.homMk (G.left.irreducibleComponentSubschemeι I)
  obtain ⟨ezLeft, hezLeft, _⟩ := existsUnique_lift_identityPoint_into_componentSubscheme G Z hZ
  obtain ⟨eiLeft, heiLeft, _⟩ := existsUnique_lift_identityPoint_into_componentSubscheme G I
    (identity_mem_identityIrreducibleComponent G)
  let eZ : 𝟙_ (SchemeOverField K) ⟶ ZOver := Over.homMk ezLeft (by
    -- The chosen identity lift still lies over the base field.
    change ezLeft ≫ G.left.irreducibleComponentSubschemeι Z ≫ G.hom =
      (𝟙_ (SchemeOverField K)).hom
    calc
      ezLeft ≫ G.left.irreducibleComponentSubschemeι Z ≫ G.hom =
          η[G].left ≫ G.hom := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) hezLeft
      _ = (𝟙_ (SchemeOverField K)).hom := Over.w η[G])
  let eI : 𝟙_ (SchemeOverField K) ⟶ IOver := Over.homMk eiLeft (by
    -- The canonical identity lift for the selected identity component is also over the base.
    change eiLeft ≫ G.left.irreducibleComponentSubschemeι I ≫ G.hom =
      (𝟙_ (SchemeOverField K)).hom
    calc
      eiLeft ≫ G.left.irreducibleComponentSubschemeι I ≫ G.hom =
          η[G].left ≫ G.hom := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) heiLeft
      _ = (𝟙_ (SchemeOverField K)).hom := Over.w η[G])
  let m : ZOver ⊗ IOver ⟶ G := (zInclusion ⊗ₘ iInclusion) ≫ μ[G]
  have heZ : eZ ≫ zInclusion = η[G] := by
    ext
    exact hezLeft
  have heI : eI ≫ iInclusion = η[G] := by
    ext
    exact heiLeft
  -- Local instance justification (proof-local temporary data): irreducibility of the component subscheme of `Z` is used only in the following product argument.
  haveI : IrreducibleSpace ZOver.left := by
    change IrreducibleSpace (G.left.irreducibleComponentSubscheme Z)
    infer_instance
  -- Local instance justification (proof-local temporary data): irreducibility of the component subscheme of `I` is used only in the following product argument.
  haveI : IrreducibleSpace IOver.left := by
    change IrreducibleSpace (G.left.irreducibleComponentSubscheme I)
    infer_instance
  -- Local instance justification (proof-local temporary data): geometric irreducibility over an algebraically closed field is used only to prove irreducibility of this product.
  haveI : GeometricallyIrreducible ZOver.hom := by
    exact GeometricallyIrreducible.of_isSepClosed (f := ZOver.hom)
  -- Local instance justification (proof-local temporary data): universal openness is used only to supply the open-map hypothesis for the pullback projection below.
  haveI : UniversallyOpen ZOver.hom := by
    infer_instance
  -- Local instance justification (proof-local temporary data): irreducibility of the product is used only to control the image of multiplication in this proof.
  haveI : IrreducibleSpace (ZOver ⊗ IOver).left := by
    change IrreducibleSpace ↥(Limits.pullback ZOver.hom IOver.hom)
    exact GeometricallyIrreducible.irreducibleSpace
      (f := Limits.pullback.snd ZOver.hom IOver.hom)
      (hf := (Limits.pullback.snd ZOver.hom IOver.hom).isOpenMap)
  have hmRangeIrreducible : IsIrreducible (Set.range m.left.base) := by
    -- The multiplication image of an irreducible source is irreducible.
    simpa [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (ZOver ⊗ IOver).left).image
        m.left.base m.left.continuous.continuousOn
  obtain ⟨W, hW, hmW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (Set.range m.left.base) hmRangeIrreducible
  let Wc : irreducibleComponents G.left := ⟨W, hW⟩
  have hZRange : Set.range zInclusion.left.base ⊆ Set.range m.left.base := by
    -- Multiplication by the lifted identity section recovers the first component inclusion.
    have hSection : lift (𝟙 ZOver) (toUnit ZOver ≫ eI) ≫ m = zInclusion := by
      have hLiftMap :
          lift (𝟙 ZOver) (toUnit ZOver ≫ eI) ≫ (zInclusion ⊗ₘ iInclusion) =
            lift (𝟙 ZOver ≫ zInclusion) ((toUnit ZOver ≫ eI) ≫ iInclusion) := by
        simpa using lift_map (𝟙 ZOver) (toUnit ZOver ≫ eI) zInclusion iInclusion
      calc
        lift (𝟙 ZOver) (toUnit ZOver ≫ eI) ≫ m =
            (lift (𝟙 ZOver) (toUnit ZOver ≫ eI) ≫ (zInclusion ⊗ₘ iInclusion)) ≫ μ[G] := by
              simp [m]
        _ = lift (𝟙 ZOver ≫ zInclusion) ((toUnit ZOver ≫ eI) ≫ iInclusion) ≫ μ[G] := by
              rw [hLiftMap]
        _ = lift zInclusion (toUnit ZOver ≫ η[G]) ≫ μ[G] := by
              rw [Category.id_comp, Category.assoc, heI]
        _ = zInclusion := by
              simpa using
                (CategoryTheory.MonObj.lift_comp_one_right
                  (B := G) (f := zInclusion) (g := toUnit ZOver))
    have hSectionLeft : (lift (𝟙 ZOver) (toUnit ZOver ≫ eI) ≫ m).left = zInclusion.left :=
      congrArg Over.Hom.left hSection
    intro x hx
    rcases hx with ⟨t, rfl⟩
    refine ⟨(lift (𝟙 ZOver) (toUnit ZOver ≫ eI)).left t, ?_⟩
    have hEval := congrArg (fun f : ZOver.left ⟶ G.left ↦ f t) hSectionLeft
    change m.left ((lift (𝟙 ZOver) (toUnit ZOver ≫ eI)).left t) = zInclusion.left t at hEval
    exact hEval
  have hIRange : Set.range iInclusion.left.base ⊆ Set.range m.left.base := by
    -- Multiplication by the lifted identity section also recovers the second component inclusion.
    have hSection : lift (toUnit IOver ≫ eZ) (𝟙 IOver) ≫ m = iInclusion := by
      have hLiftMap :
          lift (toUnit IOver ≫ eZ) (𝟙 IOver) ≫ (zInclusion ⊗ₘ iInclusion) =
            lift ((toUnit IOver ≫ eZ) ≫ zInclusion) (𝟙 IOver ≫ iInclusion) := by
        simpa using lift_map (toUnit IOver ≫ eZ) (𝟙 IOver) zInclusion iInclusion
      calc
        lift (toUnit IOver ≫ eZ) (𝟙 IOver) ≫ m =
            (lift (toUnit IOver ≫ eZ) (𝟙 IOver) ≫ (zInclusion ⊗ₘ iInclusion)) ≫ μ[G] := by
              simp [m]
        _ = lift ((toUnit IOver ≫ eZ) ≫ zInclusion) (𝟙 IOver ≫ iInclusion) ≫ μ[G] := by
              rw [hLiftMap]
        _ = lift (toUnit IOver ≫ η[G]) iInclusion ≫ μ[G] := by
              simpa [Category.assoc, heZ]
        _ = iInclusion := by
              simpa using
                (CategoryTheory.MonObj.lift_comp_one_left
                  (B := G) (f := toUnit IOver) (g := iInclusion))
    have hSectionLeft : (lift (toUnit IOver ≫ eZ) (𝟙 IOver) ≫ m).left = iInclusion.left :=
      congrArg Over.Hom.left hSection
    intro x hx
    rcases hx with ⟨t, rfl⟩
    refine ⟨(lift (toUnit IOver ≫ eZ) (𝟙 IOver)).left t, ?_⟩
    have hEval := congrArg (fun f : IOver.left ⟶ G.left ↦ f t) hSectionLeft
    change m.left ((lift (toUnit IOver ≫ eZ) (𝟙 IOver)).left t) = iInclusion.left t at hEval
    exact hEval
  have hzRangeEq : Set.range zInclusion.left.base = (Z : Set G.left) := by
    have hRangeClosed :
        Set.range (G.left.irreducibleComponentSubschemeι Z) =
          (G.left.irreducibleComponentClosed Z : Set G.left) :=
      Scheme.IdealSheafData.range_vanishingIdeal_subschemeι
        (G.left.irreducibleComponentClosed Z)
    change Set.range (G.left.irreducibleComponentSubschemeι Z) =
      (G.left.irreducibleComponentClosed Z : Set G.left)
    exact hRangeClosed
  have hiRangeEq : Set.range iInclusion.left.base = (I : Set G.left) := by
    have hRangeClosed :
        Set.range (G.left.irreducibleComponentSubschemeι I) =
          (G.left.irreducibleComponentClosed I : Set G.left) :=
      Scheme.IdealSheafData.range_vanishingIdeal_subschemeι
        (G.left.irreducibleComponentClosed I)
    change Set.range (G.left.irreducibleComponentSubschemeι I) =
      (G.left.irreducibleComponentClosed I : Set G.left)
    exact hRangeClosed
  have hZW : (Z : Set G.left) ⊆ W := by
    rw [← hzRangeEq]
    exact Set.Subset.trans hZRange hmW
  have hIW : (I : Set G.left) ⊆ W := by
    rw [← hiRangeEq]
    exact Set.Subset.trans hIRange hmW
  have hZWc : Z = Wc := by
    apply Subtype.ext
    exact Set.Subset.antisymm hZW (Z.2.2 hW.1 hZW)
  have hIWc : I = Wc := by
    apply Subtype.ext
    exact Set.Subset.antisymm hIW (I.2.2 hW.1 hIW)
  simpa [I] using (hZWc.trans hIWc.symm)

/-- Evaluating the unit section of a field-extension base change at the closed point of `Spec K`
projects to the original identity point. -/
theorem identitySection_baseChange_toSource
    {K : Type u} [Field K] [Algebra k K]
    (G : SchemeOverField k) [GrpObj G] :
    FieldExtension.toSource k K G.hom
        (η[FieldExtension.Over.baseChange k K G].left (IsLocalRing.closedPoint K)) =
      η[G].left (IsLocalRing.closedPoint k) := by
  -- Evaluating the pullback-unit normalization at the unique point of `Spec K` gives the
  -- pointwise formula needed for component lifting.
  -- TODO: turn `CategoryTheory.Functor.comp_mapGrp_one` for `Over.pullback (FieldExtension.specMap k K)`
  -- into this pointwise formula by normalizing the right-hand side through
  -- `Functor.LaxMonoidal.ε`, `pullback.lift`, and the pullback condition.
  sorry

/-- After a field extension, an irreducible component containing the identity lifts to an
irreducible component of the base change that still contains the identity and maps back to the
original component. -/
theorem liftComponentContainingIdentity
    {K : Type u} [Field K] [Algebra k K]
    (G : SchemeOverField k) [GrpObj G] (Z : irreducibleComponents G.left)
    (hZ : η[G].left (IsLocalRing.closedPoint k) ∈ (Z : Set G.left)) :
    ∃ ZK : irreducibleComponents (FieldExtension.Over.baseChange k K G).left,
      η[FieldExtension.Over.baseChange k K G].left (IsLocalRing.closedPoint K) ∈ (ZK : Set _) ∧
        FieldExtension.Irreducible.componentsMap k K G.hom ZK = Z := by
  have hpre :
      η[FieldExtension.Over.baseChange k K G].left (IsLocalRing.closedPoint K) ∈
        (FieldExtension.toSource k K G.hom) ⁻¹' (Z : Set G.left) := by
    -- The closed point of the base change projects to the original identity point.
    change
      FieldExtension.toSource k K G.hom
          (η[FieldExtension.Over.baseChange k K G].left (IsLocalRing.closedPoint K)) ∈
        (Z : Set G.left)
    rw [identitySection_baseChange_toSource (k := k) (K := K) G]
    exact hZ
  -- The inverse image of a downstairs component is the union of the components in its fibre.
  rw [FieldExtension.Irreducible.preimage_component_eq_iUnion_fiber] at hpre
  rcases Set.mem_iUnion.mp hpre with ⟨ZK, hpre⟩
  rcases Set.mem_iUnion.mp hpre with ⟨hfiber, hmem⟩
  refine ⟨ZK, hmem, ?_⟩
  -- Membership in the canonical fibre is exactly equality under `componentsMap`.
  simpa [FieldExtension.Irreducible.mem_fiber_iff] using hfiber

/-- Exactly one irreducible component of a group scheme over a field contains its identity
point. -/
theorem existsUniqueIrreducibleComponent_throughIdentity
    (G : SchemeOverField k) [GrpObj G] :
    ∃! Z : irreducibleComponents G.left,
      η[G].left (IsLocalRing.closedPoint k) ∈ (Z : Set G.left) := by
  refine ⟨identityIrreducibleComponent G, identity_mem_identityIrreducibleComponent G, ?_⟩
  · intro Z hZ
    -- Compare `Z` with the selected component after lifting both to an algebraic closure, then
    -- descend the resulting upstairs equality along `componentsMap`.
    let Zbar : irreducibleComponents (FieldExtension.Over.baseChange k (AlgebraicClosure k) G).left :=
      Classical.choose
        (liftComponentContainingIdentity (K := AlgebraicClosure k) G Z hZ)
    let Ibar : irreducibleComponents (FieldExtension.Over.baseChange k (AlgebraicClosure k) G).left :=
      Classical.choose
        (liftComponentContainingIdentity (K := AlgebraicClosure k) G
          (identityIrreducibleComponent G) (identity_mem_identityIrreducibleComponent G))
    have hZbarMem :
        η[FieldExtension.Over.baseChange k (AlgebraicClosure k) G].left
            (IsLocalRing.closedPoint (AlgebraicClosure k)) ∈
          (Zbar : Set (FieldExtension.Over.baseChange k (AlgebraicClosure k) G).left) :=
      (Classical.choose_spec
        (liftComponentContainingIdentity (K := AlgebraicClosure k) G Z hZ)).1
    have hIbarMem :
        η[FieldExtension.Over.baseChange k (AlgebraicClosure k) G].left
            (IsLocalRing.closedPoint (AlgebraicClosure k)) ∈
          (Ibar : Set (FieldExtension.Over.baseChange k (AlgebraicClosure k) G).left) :=
      (Classical.choose_spec
        (liftComponentContainingIdentity (K := AlgebraicClosure k) G
          (identityIrreducibleComponent G) (identity_mem_identityIrreducibleComponent G))).1
    have hZbarEq :
        Zbar = identityIrreducibleComponent
          (FieldExtension.Over.baseChange k (AlgebraicClosure k) G) :=
      eqIdentityIrreducibleComponentOfMem_isAlgClosed
        (G := FieldExtension.Over.baseChange k (AlgebraicClosure k) G) hZbarMem
    have hIbarEq :
        Ibar = identityIrreducibleComponent
          (FieldExtension.Over.baseChange k (AlgebraicClosure k) G) :=
      eqIdentityIrreducibleComponentOfMem_isAlgClosed
        (G := FieldExtension.Over.baseChange k (AlgebraicClosure k) G) hIbarMem
    have hZbarMap :
        FieldExtension.Irreducible.componentsMap k (AlgebraicClosure k) G.hom Zbar = Z :=
      (Classical.choose_spec
        (liftComponentContainingIdentity (K := AlgebraicClosure k) G Z hZ)).2
    have hIbarMap :
        FieldExtension.Irreducible.componentsMap k (AlgebraicClosure k) G.hom Ibar =
          identityIrreducibleComponent G :=
      (Classical.choose_spec
        (liftComponentContainingIdentity (K := AlgebraicClosure k) G
          (identityIrreducibleComponent G) (identity_mem_identityIrreducibleComponent G))).2
    calc
      Z = FieldExtension.Irreducible.componentsMap k (AlgebraicClosure k) G.hom Zbar :=
        hZbarMap.symm
      _ = FieldExtension.Irreducible.componentsMap k (AlgebraicClosure k) G.hom Ibar := by
            rw [hZbarEq, hIbarEq]
      _ = identityIrreducibleComponent G := hIbarMap

/-- Any irreducible component containing the identity point is the selected one. -/
theorem eq_identityIrreducibleComponent_of_mem
    (G : SchemeOverField k) [GrpObj G] (Z : irreducibleComponents G.left)
    (hZ : η[G].left (IsLocalRing.closedPoint k) ∈ (Z : Set G.left)) :
    Z = identityIrreducibleComponent G := by
  rcases existsUniqueIrreducibleComponent_throughIdentity G with ⟨Z₀, hZ₀, huniq⟩
  exact (huniq Z hZ).trans (huniq (identityIrreducibleComponent G)
    (identity_mem_identityIrreducibleComponent G)).symm

/-- An irreducible component of a group scheme over a field that contains the identity point is
geometrically irreducible over the field. -/
theorem geometricallyIrreducible_identityComponent
    (G : SchemeOverField k) [GrpObj G]
    (Z : irreducibleComponents G.left)
    (hZ : η[G].left (IsLocalRing.closedPoint k) ∈ (Z : Set G.left)) :
    GeometricallyIrreducible
      (G.left.irreducibleComponentSubschemeι Z ≫ G.hom) := by
  -- TODO: rewrite `Z` to `identityIrreducibleComponent G`, lift the selected component to a
  -- separable closure, prove the upstairs identity component is Galois-fixed, and then apply
  -- `FieldExtension.Galois.Irreducible.mem_fixedPoints_iff_exists_geometricallyIrreducibleComponent`.
  sorry

/-- The irreducible component selected by the identity point is geometrically irreducible. -/
instance instGeometricallyIrreducibleIdentityIrreducibleComponent
    (G : SchemeOverField k) [GrpObj G] :
    GeometricallyIrreducible
      (G.left.irreducibleComponentSubschemeι (identityIrreducibleComponent G) ≫ G.hom) := by
  simpa using
    geometricallyIrreducible_identityComponent G (identityIrreducibleComponent G)
      (identity_mem_identityIrreducibleComponent G)

end

end AlgebraicGeometry.GroupScheme
