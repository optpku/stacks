/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap99.Lemma_99_13_1_Spaces

/-!
# Families of curves as a full subcategory of fp-flat-proper spaces

The category of families of curves over schemes over a base is the full
subcategory of `FpFlatProperGroupoids` on objects whose structure morphism has
relative dimension at most `1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Objects of `FpFlatProperGroupoids S` whose structure morphism has relative
dimension at most `1`. -/
def curves (S : Scheme.{u}) : ObjectProperty (FpFlatProperGroupoids S) :=
  fun P ↦ RelativeDimensionLE P.obj.obj.obj.hom 1

/-- Membership in `curves S` is relative dimension at most `1` of the structure
morphism. -/
theorem curves_iff {S : Scheme.{u}} (P : FpFlatProperGroupoids S) :
    curves S P ↔ RelativeDimensionLE P.obj.obj.obj.hom 1 := sorry

/-- The full subcategory of `FpFlatProperGroupoids S` on families of relative
dimension at most `1`. -/
abbrev CurvesGroupoids (S : Scheme.{u}) :=
  (curves S).FullSubcategory

/-- The projection `CurvesGroupoids S ⥤ Over S`, obtained by restricting
`pFpFlatProperGroupoids`. -/
abbrev pCurvesGroupoids (S : Scheme.{u}) : CurvesGroupoids S ⥤ Over S :=
  (curves S).ι ⋙ pFpFlatProperGroupoids S

namespace CurvesGroupoids

/-- Package an `FpFlatProper` morphism of relative dimension at most `1` as an
object of `CurvesGroupoids S`. -/
def mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    CurvesGroupoids S :=
  { obj := FpFlatProperGroupoids.mk pX,
    property := (inferInstance : RelativeDimensionLE pX 1) }

/-- The underlying `FpFlatProperGroupoids` object of `mk pX` is
`FpFlatProperGroupoids.mk pX`. -/
theorem mk_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    (mk pX).obj = FpFlatProperGroupoids.mk pX := sorry

/-- The full-subcategory inclusion
`CurvesGroupoids S ⥤ FpFlatProperGroupoids S`. -/
abbrev inclusion (S : Scheme.{u}) :
    CurvesGroupoids S ⥤ FpFlatProperGroupoids S :=
  (curves S).ι

/-- The inclusion of `CurvesGroupoids` is full. -/
instance inclusion_full (S : Scheme.{u}) : (inclusion S).Full :=
  inferInstance

/-- The inclusion of `CurvesGroupoids` is faithful. -/
instance inclusion_faithful (S : Scheme.{u}) : (inclusion S).Faithful :=
  inferInstance

/-- The inclusion sends `mk pX` to `FpFlatProperGroupoids.mk pX`. -/
theorem inclusion_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] [RelativeDimensionLE pX 1] :
    (inclusion S).obj (mk pX) = FpFlatProperGroupoids.mk pX := sorry

end CurvesGroupoids

/-- The projection `pCurvesGroupoids` sends `mk pX` to the scheme `U` over
`S`. -/
theorem pCurvesGroupoids_obj {S : Scheme.{u}} {U : Over S}
    {X : AlgebraicSpace S} (pX : X ⟶ ofOver U) [FpFlatProper pX]
    [RelativeDimensionLE pX 1] :
    (pCurvesGroupoids S).obj (CurvesGroupoids.mk pX) = U := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
