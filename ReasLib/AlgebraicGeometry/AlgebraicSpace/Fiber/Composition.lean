module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Canonical maps between fibres of composable algebraic-space morphisms

The fibre of a composite over a field-valued point maps canonically to the
fibre of the second morphism over that point, preserving both projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical morphism from the fibre of `f ≫ g` over a field-valued point
`p` of `Z` to the fibre of `g` over `p`. -/
noncomputable def compFiberToBaseFiber {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : FieldValuedPoint Z) :
    pullbackAlongScheme (f ≫ g) p.hom ⟶ pullbackAlongScheme g p.hom :=
  (pullback.lift
      (pullbackAlongScheme.fst (f ≫ g) p.hom ≫ f)
      (pullbackAlongScheme.snd (f ≫ g) p.hom)
      (by
        rw [Category.assoc]
        exact pullbackAlongScheme.fst_comp (f ≫ g) p.hom) :
    (pullbackAlongScheme (f ≫ g) p.hom).functorOfPoints ⟶
      (pullbackAlongScheme g p.hom).functorOfPoints)

/-- The composite-fibre map sends the projection to `Y` to the original map `f`. -/
theorem compFiberToBaseFiber_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : FieldValuedPoint Z) :
    compFiberToBaseFiber f g p ≫ pullbackAlongScheme.fst g p.hom =
      pullbackAlongScheme.fst (f ≫ g) p.hom ≫ f := by
  unfold compFiberToBaseFiber pullbackAlongScheme.fst pullbackAlongSchemeFstNat
  exact pullback.lift_fst
    (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (g : Y.functorOfPoints ⟶ Z.functorOfPoints))
    (g := (p.hom : (ofOver (Over.mk p.structureHom)).functorOfPoints ⟶ Z.functorOfPoints))
    _ _ _

/-- The composite-fibre map preserves the projection to `Spec(k)`. -/
theorem compFiberToBaseFiber_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : FieldValuedPoint Z) :
    compFiberToBaseFiber f g p ≫ pullbackAlongScheme.snd g p.hom =
      pullbackAlongScheme.snd (f ≫ g) p.hom := by
  unfold compFiberToBaseFiber pullbackAlongScheme.snd pullbackAlongSchemeSndNat
  exact pullback.lift_snd
    (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (g : Y.functorOfPoints ⟶ Z.functorOfPoints))
    (g := (p.hom : (ofOver (Over.mk p.structureHom)).functorOfPoints ⟶ Z.functorOfPoints))
    _ _ _

end AlgebraicGeometry.AlgebraicSpace
