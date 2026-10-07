module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalModels.Concrete

/-!
# Equivalence of concrete diagonal models

This file constructs the explicit equivalence between the direct diagonal model and the iterated
categorical-pullback model. Computation rules and derived properties are provided in separate
modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Prod
open CategoricalPullback
open scoped CategoricalPullback

universe vC vS uC uS

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable (G₁ G₂ : C ⥤ S)

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace CategoricalPullback.DiagonalModel.equivalence.Implementation

/-- The explicit inverse image of an iterated-pullback object. -/
private def inverseObj
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    CategoricalPullback.DiagonalModel.direct G₁ G₂ :=
  let ψ₁ := (CategoryTheory.Prod.fst C C).mapIso X.iso
  let ψ₂ := (CategoryTheory.Prod.snd C C).mapIso X.iso
  { fst := X.snd
    snd := G₁.obj X.fst.fst
    iso := Iso.prod (G₁.mapIso ψ₁.symm)
      (G₂.mapIso ψ₂.symm ≪≫ X.fst.iso.symm) }

/-- Compatibility of the explicit inverse map with the diagonal-model structural isomorphisms. -/
private theorem inverseMapCompatibility
    {X Y : CategoricalPullback.DiagonalModel.iterated G₁ G₂} (f : X ⟶ Y) :
    (G₁.prod' G₂).map f.snd ≫ (inverseObj G₁ G₂ Y).iso.hom =
      (inverseObj G₁ G₂ X).iso.hom ≫
        (Functor.diag S).map (G₁.map f.fst.fst) := sorry

/-- The explicit inverse action on morphisms. -/
private def inverseMap
    {X Y : CategoricalPullback.DiagonalModel.iterated G₁ G₂} (f : X ⟶ Y) :
    inverseObj G₁ G₂ X ⟶ inverseObj G₁ G₂ Y where
  fst := f.snd
  snd := G₁.map f.fst.fst
  w := inverseMapCompatibility G₁ G₂ f

/-- The explicit inverse action preserves identity morphisms. -/
private theorem inverseMapId
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    inverseMap G₁ G₂ (𝟙 X) =
      𝟙 (inverseObj G₁ G₂ X) := sorry

/-- The explicit inverse action preserves composition. -/
private theorem inverseMapComp
    {X Y Z : CategoricalPullback.DiagonalModel.iterated G₁ G₂}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseMap G₁ G₂ (f ≫ g) =
      inverseMap G₁ G₂ f ≫ inverseMap G₁ G₂ g := sorry

/-- The explicit inverse functor from the iterated model to the diagonal model. -/
private def inverse :
    CategoricalPullback.DiagonalModel.iterated G₁ G₂ ⥤
      CategoricalPullback.DiagonalModel.direct G₁ G₂ where
  obj := inverseObj G₁ G₂
  map := inverseMap G₁ G₂
  map_id := inverseMapId G₁ G₂
  map_comp := inverseMapComp G₁ G₂

/-- Compatibility needed for the unit component of the concrete model equivalence. -/
private theorem unitAppCompatibility
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    (G₁.prod' G₂).map (𝟙 X.fst) ≫
        ((CategoricalPullback.DiagonalModel.comparison G₁ G₂ ⋙ inverse G₁ G₂).obj X).iso.hom =
      X.iso.hom ≫
        (Functor.diag S).map (((CategoryTheory.Prod.fst S S).mapIso X.iso).symm.hom) := sorry

/-- The unit component for the concrete model equivalence. -/
private def unitApp
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    X ≅ (CategoricalPullback.DiagonalModel.comparison G₁ G₂ ⋙ inverse G₁ G₂).obj X :=
  CategoricalPullback.mkIso (Iso.refl _)
    ((CategoryTheory.Prod.fst S S).mapIso X.iso).symm (unitAppCompatibility G₁ G₂ X)

/-- Naturality of the concrete model equivalence unit. -/
private theorem unitNaturality
    {X Y : CategoricalPullback.DiagonalModel.direct G₁ G₂} (f : X ⟶ Y) :
    (𝟭 (CategoricalPullback.DiagonalModel.direct G₁ G₂)).map f ≫
        (unitApp G₁ G₂ Y).hom =
      (unitApp G₁ G₂ X).hom ≫
        (CategoricalPullback.DiagonalModel.comparison G₁ G₂ ⋙ inverse G₁ G₂).map f := sorry

/-- The unit isomorphism for the explicit equivalence of the two concrete models. -/
private def unitIso :
    𝟭 (CategoricalPullback.DiagonalModel.direct G₁ G₂) ≅
      CategoricalPullback.DiagonalModel.comparison G₁ G₂ ⋙ inverse G₁ G₂ :=
  NatIso.ofComponents (unitApp G₁ G₂)
    (unitNaturality G₁ G₂)

/-- Compatibility for the inner-pullback component of the concrete model counit. -/
private theorem counitInnerCompatibility
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    G₁.map ((CategoryTheory.Prod.fst C C).mapIso X.iso).inv ≫ X.fst.iso.hom =
      ((inverse G₁ G₂ ⋙ CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).fst.iso.hom ≫
        G₂.map ((CategoryTheory.Prod.snd C C).mapIso X.iso).inv := sorry

/-- The inner-pullback isomorphism in the counit. -/
private def counitInnerIso
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((inverse G₁ G₂ ⋙ CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).fst ≅ X.fst :=
  CategoricalPullback.mkIso ((CategoryTheory.Prod.fst C C).mapIso X.iso).symm
    ((CategoryTheory.Prod.snd C C).mapIso X.iso).symm (counitInnerCompatibility G₁ G₂ X)

/-- Compatibility needed to combine the inner counit isomorphism with the identity on `C₃`. -/
private theorem counitAppCompatibility
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)).map
          (counitInnerIso G₁ G₂ X).hom ≫ X.iso.hom =
      ((inverse G₁ G₂ ⋙ CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).iso.hom ≫
        (Functor.diag C).map (𝟙 X.snd) := sorry

/-- The counit component for the concrete model equivalence. -/
private def counitApp
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    (inverse G₁ G₂ ⋙ CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X ≅ X :=
  CategoricalPullback.mkIso (counitInnerIso G₁ G₂ X) (Iso.refl _)
    (counitAppCompatibility G₁ G₂ X)

/-- Naturality of the concrete model equivalence counit. -/
private theorem counitNaturality
    {X Y : CategoricalPullback.DiagonalModel.iterated G₁ G₂} (f : X ⟶ Y) :
    (inverse G₁ G₂ ⋙ CategoricalPullback.DiagonalModel.comparison G₁ G₂).map f ≫
        (counitApp G₁ G₂ Y).hom =
      (counitApp G₁ G₂ X).hom ≫
        (𝟭 (CategoricalPullback.DiagonalModel.iterated G₁ G₂)).map f := sorry

/-- The counit isomorphism for the explicit equivalence of the two concrete models. -/
private def counitIso :
    inverse G₁ G₂ ⋙ CategoricalPullback.DiagonalModel.comparison G₁ G₂ ≅
      𝟭 (CategoricalPullback.DiagonalModel.iterated G₁ G₂) :=
  NatIso.ofComponents (counitApp G₁ G₂)
    (counitNaturality G₁ G₂)

/-- The triangle identity for the explicit concrete-model unit and counit. -/
private theorem triangle
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    (CategoricalPullback.DiagonalModel.comparison G₁ G₂).map ((unitIso G₁ G₂).hom.app X) ≫
        (counitIso G₁ G₂).hom.app
          ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X) =
      𝟙 ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X) := sorry

end CategoricalPullback.DiagonalModel.equivalence.Implementation

/-- The canonical equivalence between the diagonal and iterated concrete models. -/
def CategoricalPullback.DiagonalModel.equivalence :
    CategoricalPullback.DiagonalModel.direct G₁ G₂ ≌
      CategoricalPullback.DiagonalModel.iterated G₁ G₂ where
  functor := CategoricalPullback.DiagonalModel.comparison G₁ G₂
  inverse := CategoricalPullback.DiagonalModel.equivalence.Implementation.inverse G₁ G₂
  unitIso := CategoricalPullback.DiagonalModel.equivalence.Implementation.unitIso G₁ G₂
  counitIso := CategoricalPullback.DiagonalModel.equivalence.Implementation.counitIso G₁ G₂
  functor_unitIso_comp :=
    CategoricalPullback.DiagonalModel.equivalence.Implementation.triangle G₁ G₂

end

end CategoryTheory.Limits
