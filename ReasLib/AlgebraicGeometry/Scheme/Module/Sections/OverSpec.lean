module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Pullback of global sections over an affine base

This file bundles pullback on global sections as a linear map over the coordinate ring of an
affine base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R]
variable {X Y : Scheme.{u}}

/-- Pullback of global sections along a morphism over `Spec R` commutes with the action of
`R`. -/
theorem globalSectionsPullback_smul
    (f : Y ⟶ Spec (CommRingCat.of R)) (g : X ⟶ Y) (F : Y.Modules)
    (r : R) (s : Scheme.Hom.globalSectionsMod f F) :
    (globalSectionsPullback g F).hom
        ((Scheme.Hom.globalSectionsMod f F).isModule.toSMul.smul r s) =
      (Scheme.Hom.globalSectionsMod
        (g ≫ f) ((pullback g).obj F)).isModule.toSMul.smul
          r ((globalSectionsPullback g F).hom s) := sorry

/-- Pullback along `g : X ⟶ Y` gives an `R`-linear map on global sections when `Y` is mapped
to `Spec R`. -/
noncomputable def globalSectionsPullbackLinear
    (f : Y ⟶ Spec (CommRingCat.of R)) (g : X ⟶ Y) (F : Y.Modules) :
    Scheme.Hom.globalSectionsMod f F ⟶
      Scheme.Hom.globalSectionsMod (g ≫ f) ((pullback g).obj F) :=
  let source := Scheme.Hom.globalSectionsMod f F
  let target :=
    Scheme.Hom.globalSectionsMod (g ≫ f) ((pullback g).obj F)
  @ModuleCat.ofHom R _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := (globalSectionsPullback g F).hom
      map_add' := (globalSectionsPullback g F).hom.map_add
      map_smul' := globalSectionsPullback_smul f g F }

end AlgebraicGeometry.Scheme.Modules
