/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Group.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Pullback

/-!
# Tangent spaces of group schemes

This file records the behavior of the tangent map of group multiplication at the identity.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Pullback

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GroupTangent

/-- The tangent space of `G ⊗ G` at the pullback point selected by the two identity sections
agrees with the tangent space at the explicit pair of identity points. -/
theorem unitPair_tangent_eq
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    tangentSpaceAt (G ⊗ G).hom
      (pointOfBaseResidueFieldMapBijective G.hom G.hom
        (η[G].left s) (η[G].left s) rfl
        (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)) =
      tangentSpaceAt (G ⊗ G).hom ((lift η[G] η[G]).left s) := by
  simpa using
    congrArg (fun z ↦ tangentSpaceAt (G ⊗ G).hom z) (unitPair_eq_selected G s).symm

/-- The source tangent space for multiplication at the identity pair is the tangent space of
`G ⊗ G` at that pair. -/
theorem mul_unitPair_tangentSource_eq
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    tangentSpaceAt (G ⊗ G).hom ((lift η[G] η[G]).left s) =
      tangentSpaceAt (μ[G].left ≫ G.hom) ((lift η[G] η[G]).left s) := by
  simpa using
    congrArg
      (fun f : (G ⊗ G).left ⟶ S ↦ tangentSpaceAt f ((lift η[G] η[G]).left s))
      (Over.w μ[G]).symm

/-- The target tangent space for multiplication at the identity pair is the tangent space at the
identity point. -/
theorem mul_unitPair_tangentTarget_eq
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    tangentSpaceAt G.hom (μ[G].left ((lift η[G] η[G]).left s)) =
      tangentSpaceAt G.hom (η[G].left s) := by
  simpa using congrArg (fun z ↦ tangentSpaceAt G.hom z) (mul_unitPair G s)

/-- The identity point of a group scheme lies over the chosen base point. -/
private theorem unitPoint_base_eq
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    G.hom (η[G].left s) = s := by
  -- Evaluating the section identity `η ≫ G.hom = 𝟙` at `s` identifies the base point of the
  -- identity section.
  change TopCat.Hom.hom G.hom.base (TopCat.Hom.hom (η[G].left).base s) = s
  exact congrArg (fun k : S ⟶ S ↦ TopCat.Hom.hom k.base s) (Over.w η[G])

/-- The pullback point selected by the two identity sections also lies over `s`. -/
private theorem selectedUnitPair_base_eq
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    let xy :=
      pointOfBaseResidueFieldMapBijective G.hom G.hom
        (η[G].left s) (η[G].left s) rfl
        (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
    (pullback.fst G.hom G.hom ≫ G.hom) xy = s := by
  let xy :=
    pointOfBaseResidueFieldMapBijective G.hom G.hom
      (η[G].left s) (η[G].left s) rfl
      (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
  -- The selected pullback point projects to the identity point, which already lies over `s`.
  have hfst :
      pullback.fst G.hom G.hom xy = η[G].left s := by
    simpa [xy] using
      pointOfBaseResidueFieldMapBijective_fst
        G.hom G.hom (η[G].left s) (η[G].left s) rfl
        (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
  exact (congrArg G.hom hfst).trans (unitPoint_base_eq G s)

/-- The right-unit section of multiplication on a group scheme. -/
private abbrev rightUnitSection {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    G.left ⟶ (G ⊗ G).left :=
  (lift (𝟙 G) (toUnit G ≫ η[G])).left

/-- The left-unit section of multiplication on a group scheme. -/
private abbrev leftUnitSection {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    G.left ⟶ (G ⊗ G).left :=
  (lift (toUnit G ≫ η[G]) (𝟙 G)).left

/-- Multiplication retracts the right-unit section on the underlying schemes. -/
private theorem rightUnitSection_retract
    {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    rightUnitSection G ≫ μ[G].left = 𝟙 G.left := by
  -- The monoid-object right-unit law descends to the underlying scheme morphisms.
  have hsec_over : lift (𝟙 G) (toUnit G ≫ η[G]) ≫ μ[G] = 𝟙 G := by
    simpa using
      (CategoryTheory.MonObj.lift_comp_one_right
        (B := G) (f := 𝟙 G) (g := toUnit G))
  exact congrArg Over.Hom.left hsec_over

/-- Multiplication retracts the left-unit section on the underlying schemes. -/
private theorem leftUnitSection_retract
    {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    leftUnitSection G ≫ μ[G].left = 𝟙 G.left := by
  -- The monoid-object left-unit law descends to the underlying scheme morphisms.
  have hsec_over : lift (toUnit G ≫ η[G]) (𝟙 G) ≫ μ[G] = 𝟙 G := by
    simpa using
      (CategoryTheory.MonObj.lift_comp_one_left
        (B := G) (f := toUnit G) (g := 𝟙 G))
  exact congrArg Over.Hom.left hsec_over

/-- The right-unit section induces a bijection on residue fields at the identity point. -/
private theorem rightUnitSection_residueFieldMap_bijective
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    Function.Bijective ((rightUnitSection G).residueFieldMap (η[G].left s)).hom := by
  -- Any section induces a bijection on residue fields at the point where it is evaluated.
  exact AlgebraicGeometry.Scheme.Hom.section_residueFieldMap_bijective
    (e := rightUnitSection G) (f := μ[G].left)
    (hsec := rightUnitSection_retract G) (y := η[G].left s)

/-- The left-unit section induces a bijection on residue fields at the identity point. -/
private theorem leftUnitSection_residueFieldMap_bijective
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    Function.Bijective ((leftUnitSection G).residueFieldMap (η[G].left s)).hom := by
  -- The same section argument applies to the left-unit section.
  exact AlgebraicGeometry.Scheme.Hom.section_residueFieldMap_bijective
    (e := leftUnitSection G) (f := μ[G].left)
    (hsec := leftUnitSection_retract G) (y := η[G].left s)

/-- Transporting the multiplication tangent map across the three unit-pair identifications
preserves addition of tangent vectors. -/
private theorem mulUnitPairTransportAdd
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (D₁ D₂ : tangentSpaceAt (G ⊗ G).hom
      (pointOfBaseResidueFieldMapBijective G.hom G.hom
        (η[G].left s) (η[G].left s) rfl
        (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s))) :
    cast (mul_unitPair_tangentTarget_eq G s)
      (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
        (mul_residueFieldMap_bijective G s)
        (cast (mul_unitPair_tangentSource_eq G s)
          (cast (unitPair_tangent_eq G s) (D₁ + D₂)))) =
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s) D₁))) +
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s) D₂))) := by
  -- TODO: normalize the three casts by eliminating the underlying point and morphism equalities
  -- `unitPair_eq_selected`, `Over.w μ[G]`, and `mul_unitPair`, then the goal reduces to
  -- `LinearMap.map_add` for `relativeTangentMapAt μ[G].left`.
  sorry

/-- The explicit transport formula for the tangent map of multiplication at the identity pair. -/
private theorem mul_apply_transport {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (v w : tangentSpaceAt G.hom (η[G].left s)) :
    cast (mul_unitPair_tangentTarget_eq G s)
      (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
        (mul_residueFieldMap_bijective G s)
        (cast (mul_unitPair_tangentSource_eq G s)
          (cast (unitPair_tangent_eq G s)
            (pullbackTangentCopairing G.hom G.hom
              (η[G].left s) (η[G].left s) rfl
              (unit_residueFieldMap_bijective G s)
              (unit_residueFieldMap_bijective G s)
              (v, w))))) = v + w := by
  -- Route correction: first rewrite the pullback copairing as the sum of the two unit-section
  -- summands, and only then isolate the right-unit and left-unit tangent computations.
  have hcopair :
      cast (mul_unitPair_tangentSource_eq G s)
          (cast (unitPair_tangent_eq G s)
            (pullbackTangentCopairing G.hom G.hom
              (η[G].left s) (η[G].left s) rfl
              (unit_residueFieldMap_bijective G s)
              (unit_residueFieldMap_bijective G s)
              (v, w))) =
        cast (mul_unitPair_tangentSource_eq G s)
          (cast (unitPair_tangent_eq G s)
            (pullbackTangentInl G.hom G.hom
              (η[G].left s) (η[G].left s) rfl
              (unit_residueFieldMap_bijective G s)
              (unit_residueFieldMap_bijective G s)
              v +
             pullbackTangentInr G.hom G.hom
              (η[G].left s) (η[G].left s) rfl
              (unit_residueFieldMap_bijective G s)
              (unit_residueFieldMap_bijective G s)
              w)) := by
    -- The pullback copairing is definitionally the coprod of the two summand maps.
    rfl
  have hinl :
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s)
              (pullbackTangentInl G.hom G.hom
                (η[G].left s) (η[G].left s) rfl
                (unit_residueFieldMap_bijective G s)
                (unit_residueFieldMap_bijective G s)
                v)))) = v := by
    -- TODO: replace the current pullback inclusion by the tangent map of `rightUnitSection G`,
    -- transport it along `rightUnitSection_apply_eq_unitPair`, and then apply the generic
    -- section-retraction identity coming from `rightUnitSection_retract`.
    sorry
  have hinr :
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s)
              (pullbackTangentInr G.hom G.hom
                (η[G].left s) (η[G].left s) rfl
                (unit_residueFieldMap_bijective G s)
                (unit_residueFieldMap_bijective G s)
                w)))) = w := by
    -- TODO: symmetrically rewrite the second summand through `leftUnitSection G`,
    -- normalize via `leftUnitSection_apply_eq_unitPair`, and finish using
    -- `leftUnitSection_retract`.
    sorry
  -- The remaining step is linear algebra: package the transport bookkeeping once, then use the
  -- two summand computations.
  calc
    cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s)
              (pullbackTangentCopairing G.hom G.hom
                (η[G].left s) (η[G].left s) rfl
                (unit_residueFieldMap_bijective G s)
                (unit_residueFieldMap_bijective G s)
                (v, w))))) =
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s)
              (pullbackTangentInl G.hom G.hom
                (η[G].left s) (η[G].left s) rfl
                (unit_residueFieldMap_bijective G s)
                (unit_residueFieldMap_bijective G s)
                v +
               pullbackTangentInr G.hom G.hom
                (η[G].left s) (η[G].left s) rfl
                (unit_residueFieldMap_bijective G s)
                (unit_residueFieldMap_bijective G s)
                w)))) := by
      rw [hcopair]
    _ =
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s)
              (pullbackTangentInl G.hom G.hom
                (η[G].left s) (η[G].left s) rfl
                (unit_residueFieldMap_bijective G s)
                (unit_residueFieldMap_bijective G s)
                v)))) +
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s)
            (cast (unitPair_tangent_eq G s)
              (pullbackTangentInr G.hom G.hom
                (η[G].left s) (η[G].left s) rfl
                (unit_residueFieldMap_bijective G s)
                (unit_residueFieldMap_bijective G s)
                w)))) := by
      -- Route correction: isolate the cast/add normalization once instead of rebuilding these
      -- transports at the end of each summand proof.
      exact
        mulUnitPairTransportAdd G s
          (pullbackTangentInl G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s)
            (unit_residueFieldMap_bijective G s)
            v)
          (pullbackTangentInr G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s)
            (unit_residueFieldMap_bijective G s)
            w)
    _ = v + w := by
      rw [hinl, hinr]

/-- For a group scheme over `S`, the tangent map of multiplication at the pair of identity
points sends the tangent vector determined by `(v, w)` to `v + w`. -/
theorem mul_apply {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (v w : tangentSpaceAt G.hom (η[G].left s)) :
    let unitPairTangent :=
      cast (unitPair_tangent_eq G s)
        (pullbackTangentCopairing G.hom G.hom
          (η[G].left s) (η[G].left s) rfl
          (unit_residueFieldMap_bijective G s)
          (unit_residueFieldMap_bijective G s)
          (v, w))
    let mulTangent :=
      cast (mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (mul_residueFieldMap_bijective G s)
          (cast (mul_unitPair_tangentSource_eq G s) unitPairTangent))
    mulTangent = v + w := by
  simpa using mul_apply_transport G s v w

end AlgebraicGeometry.Scheme.GroupTangent
