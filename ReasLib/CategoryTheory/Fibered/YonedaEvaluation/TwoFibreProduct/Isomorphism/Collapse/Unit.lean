module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse.Computations

/-!
# The collapse unit

This leaf constructs the explicit unit from a literal two-fibre-product object to its
deterministic reconstruction.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

namespace collapse
namespace unitComponent

/-- The reconstructed object's base is the domain of the literal slice object. -/
@[simp, stacks 04SI "unit target base readout"]
theorem targetBase (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.baseObj
        (((collapse X x y) ⋙ (inverse X x y)).obj Q) =
      (isomSection.slice X x y Q).left := sorry

/-- The reconstructed middle object is the left Yoneda value at the literal slice object. -/
@[simp, stacks 04SI "unit target first readout"]
theorem targetFst (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.fstObj
        (((collapse X x y) ⋙ (inverse X x y)).obj Q) =
      (yonedaMap X x).obj (isomSection.slice X x y Q) := sorry

/-- The reconstructed slice object is the literal slice object. -/
@[simp, stacks 04SI "unit target second readout"]
theorem targetSnd (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.sndObj
        (((collapse X x y) ⋙ (inverse X x y)).obj Q) =
      isomSection.slice X x y Q := sorry

/-- The base comparison from a literal source object to the deterministic reconstruction of its
collapsed section. -/
@[stacks 04SI "unit base comparison"]
noncomputable def base (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.baseObj Q ≅
      BasedCategory.PseudoPullback.baseObj
        (((collapse X x y) ⋙ (inverse X x y)).obj Q) :=
  (BasedCategory.PseudoPullback.sndBaseIso Q).symm

/-- The middle-object comparison from a literal source object to its deterministic
reconstruction. -/
@[stacks 04SI "unit first comparison"]
noncomputable def fst (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.fstObj Q ≅
      BasedCategory.PseudoPullback.fstObj
        (((collapse X x y) ⋙ (inverse X x y)).obj Q) :=
  isomSection.leftIso X x y Q

/-- The slice component is unchanged by collapse followed by deterministic reconstruction. -/
@[stacks 04SI "unit second comparison"]
noncomputable def snd (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.sndObj Q ≅
      BasedCategory.PseudoPullback.sndObj
        (((collapse X x y) ⋙ (inverse X x y)).obj Q) :=
  Iso.refl _
/- Data audit: reconstruction stores the displayed base, middle object, and slice object directly.
The unit therefore uses the source object's stored base isomorphism, the projected outer
comparison, and a reflexive slice comparison; the computation theorems above are readouts only. -/

/-- The middle-object comparison lies over the displayed base comparison. -/
@[stacks 04SI "unit first verticality"]
theorem fst.isHomLift (Q : (source X x y).obj) :
    X.p.IsHomLift (base X x y Q).hom (fst X x y Q).hom := sorry

/-- The unchanged slice component lies over the displayed base comparison. -/
@[stacks 04SI "unit second verticality"]
theorem snd.isHomLift (Q : (source X x y).obj) :
    (FiberedCategoryOver.TwoFibreProduct.Isomorphism.slice U).p.IsHomLift
      (base X x y Q).hom (snd X x y Q).hom := sorry

/-- The deterministic unit components respect the two outer comparison morphisms. -/
@[stacks 04SI "unit comparison compatibility"]
theorem compatibility (Q : (source X x y).obj) :
    CommSq
      ((diagonal X).toFunctor.map (fst X x y Q).hom)
      (BasedCategory.PseudoPullback.comparison Q)
      (BasedCategory.PseudoPullback.comparison
        (((collapse X x y) ⋙ (inverse X x y)).obj Q))
      ((yonedaPair X x y).toFunctor.map (snd X x y Q).hom) := sorry

end unitComponent

/-- A literal two-fibre-product object is explicitly isomorphic to the deterministic
reconstruction of its collapsed isomorphism section. -/
@[stacks 04SI "collapse unit component"]
noncomputable def unitComponent (Q : (source X x y).obj) :
    Q ≅ ((collapse X x y) ⋙ (inverse X x y)).obj Q :=
  BasedCategory.PseudoPullback.mkIso (unitComponent.base X x y Q)
    (unitComponent.fst X x y Q) (unitComponent.snd X x y Q)
    (unitComponent.fst.isHomLift X x y Q)
    (unitComponent.snd.isHomLift X x y Q)
    (unitComponent.compatibility X x y Q)

namespace unitComponent.hom

/-- The base map of the explicit unit component. -/
@[simp, stacks 04SI "unit forward base readout"]
theorem base (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.baseMap (unitComponent X x y Q).hom =
      (unitComponent.base X x y Q).hom := sorry

/-- The first map of the explicit unit component. -/
@[simp, stacks 04SI "unit forward first readout"]
theorem fst (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.fstMap (unitComponent X x y Q).hom =
      (unitComponent.fst X x y Q).hom := sorry

/-- The second map of the explicit unit component. -/
@[simp, stacks 04SI "unit forward second readout"]
theorem snd (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.sndMap (unitComponent X x y Q).hom =
      (unitComponent.snd X x y Q).hom := sorry

end unitComponent.hom

namespace unitComponent.inv

/-- The base map of the inverse unit component. -/
@[simp, stacks 04SI "unit inverse base readout"]
theorem base (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.baseMap (unitComponent X x y Q).inv =
      (unitComponent.base X x y Q).inv := sorry

/-- The first map of the inverse unit component. -/
@[simp, stacks 04SI "unit inverse first readout"]
theorem fst (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.fstMap (unitComponent X x y Q).inv =
      (unitComponent.fst X x y Q).inv := sorry

/-- The second map of the inverse unit component. -/
@[simp, stacks 04SI "unit inverse second readout"]
theorem snd (Q : (source X x y).obj) :
    BasedCategory.PseudoPullback.sndMap (unitComponent X x y Q).inv =
      (unitComponent.snd X x y Q).inv := sorry

end unitComponent.inv

namespace unitComponent

/-- The explicit collapse unit components are natural in literal source morphisms. -/
@[stacks 04SI "unit component naturality"]
theorem naturality {Q R : (source X x y).obj} (f : Q ⟶ R) :
    f ≫ (collapse.unitComponent X x y R).hom =
      (collapse.unitComponent X x y Q).hom ≫
        ((collapse X x y) ⋙ (inverse X x y)).map f := sorry

/-- Every collapse unit component is vertical over the identity slice arrow. -/
@[stacks 04SI "unit component verticality"]
theorem isHomLift (Q : (source X x y).obj) :
    (sourceSetoids X x y).p.IsHomLift
      (𝟙 ((sourceSetoids X x y).p.obj Q))
      (collapse.unitComponent X x y Q).hom := sorry

end unitComponent

/-- The explicit unit from the identity on the literal source to collapse followed by its
deterministic inverse. -/
@[stacks 04SI "collapse unit isomorphism"]
noncomputable def unitIso :
    𝟭 (sourceSetoids X x y).toBasedCategory ≅
      collapse X x y ⋙ inverse X x y :=
  BasedNatIso.ofComponents (unitComponent X x y)
    (unitComponent.naturality X x y) (unitComponent.isHomLift X x y)

namespace unitIso.hom

/-- The forward component of the packaged collapse unit. -/
@[simp, stacks 04SI "unit isomorphism forward readout"]
theorem app (Q : (source X x y).obj) :
    (unitIso X x y).hom.app Q = (unitComponent X x y Q).hom := sorry

end unitIso.hom

namespace unitIso.inv

/-- The inverse component of the packaged collapse unit. -/
@[simp, stacks 04SI "unit isomorphism inverse readout"]
theorem app (Q : (source X x y).obj) :
    (unitIso X x y).inv.app Q = (unitComponent X x y Q).inv := sorry

end unitIso.inv
end collapse
end FiberedCategoryOver.TwoFibreProduct.Isomorphism
end CategoryTheory
