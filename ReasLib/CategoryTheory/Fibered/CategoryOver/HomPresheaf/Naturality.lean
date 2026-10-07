module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of fiberwise Hom-presheaf maps

This file gives the `2`-cell, endpoint, owner-isomorphism, and equivalence API
for `FiberedCategoryOver.Hom.presheafHomMap`.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

namespace FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- Hom-presheaf maps commute with a `2`-morphism between their owning
morphisms, acting at both endpoints in the target fiber. -/
@[stacks 042V "naturality of fixed-universe Hom-presheaf maps"]
theorem presheafHomMap.natural
    {F G : X ⟶ Y} (τ : F ⟶ G) {U : C} (x y : X.p.Fiber U) :
    presheafHomMap F x y ≫
        Pseudofunctor.PresheafHom.Postcomp.map
          (Functor.fiberPseudofunctor Y.p)
          ((FiberedCategoryOver.fiberNatTrans τ U).app y) =
      presheafHomMap G x y ≫
        Pseudofunctor.PresheafHom.Precomp.map
          (Functor.fiberPseudofunctor Y.p)
          ((FiberedCategoryOver.fiberNatTrans τ U).app x) := sorry

/-- The canonical Hom-presheaf map is natural in isomorphisms of both
endpoint objects. -/
@[stacks 042V "endpoint naturality of Hom-presheaf maps"]
theorem presheafHomMap.endpoints.iso
    (F : X ⟶ Y) {U : C} {x₁ x₂ y₁ y₂ : X.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (Pseudofunctor.PresheafHom.Congr.iso
        (Functor.fiberPseudofunctor X.p) ex ey).hom ≫
        presheafHomMap F x₂ y₂ =
      presheafHomMap F x₁ y₁ ≫
        (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctor F U).mapIso ex) ((fiberFunctor F U).mapIso ey)).hom := sorry

/-- Pointwise form of `presheafHomMap.endpoints.iso`. -/
@[stacks 042V "pointwise endpoint naturality of Hom-presheaf maps"]
theorem presheafHomMap.endpoints.iso.app
    (F : X ⟶ Y) {U : C} {x₁ x₂ y₁ y₂ : X.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ)
    (f : ((Functor.fiberPseudofunctor X.p).presheafHom x₁ y₁).obj W) :
    (presheafHomMap F x₂ y₂).app W
        ((Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor X.p) ex ey).hom.app W f) =
      (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctor F U).mapIso ex) ((fiberFunctor F U).mapIso ey)).hom.app W
        ((presheafHomMap F x₁ y₁).app W f) := sorry

/-- Hom-presheaf maps attached to isomorphic morphisms of fibred categories
differ by the induced endpoint conjugation in the target fiber. -/
@[stacks 02ZA "invariance of Hom-presheaf maps under isomorphic owners"]
theorem presheafHomMap.ownerIso
    {F G : X ⟶ Y} (e : F ≅ G) {U : C} (x y : X.p.Fiber U) :
    presheafHomMap F x y ≫
        (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctorIso e U).app x) ((fiberFunctorIso e U).app y)).hom =
      presheafHomMap G x y := sorry

/-- Pointwise form of `presheafHomMap.ownerIso`. -/
@[stacks 02ZA "pointwise owner-isomorphism invariance of Hom-presheaf maps"]
theorem presheafHomMap.ownerIso.app
    {F G : X ⟶ Y} (e : F ≅ G) {U : C} (x y : X.p.Fiber U)
    (W : (Over U)ᵒᵖ)
    (f : ((Functor.fiberPseudofunctor X.p).presheafHom x y).obj W) :
    (presheafHomMap G x y).app W f =
      (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctorIso e U).app x) ((fiberFunctorIso e U).app y)).hom.app W
        ((presheafHomMap F x y).app W f) := sorry

/-- Any isomorphism-invariant morphism property holds for the Hom-presheaf
maps of two isomorphic morphisms of fibred categories simultaneously. -/
@[stacks 02ZA "property invariance for isomorphic Hom-presheaf owners"]
theorem presheafHomMap.ownerIso.mem_iff
    {U : C} (P : MorphismProperty ((Over U)ᵒᵖ ⥤ Type vS)) [P.RespectsIso]
    {F G : X ⟶ Y} (e : F ≅ G) (x y : X.p.Fiber U) :
    P (presheafHomMap F x y) ↔ P (presheafHomMap G x y) := sorry

/-- A morphism of fibred categories is fully faithful exactly when all its
canonical fiberwise Hom-presheaf maps are isomorphisms. -/
@[stacks 04WQ "full faithfulness via fixed-universe Hom-presheaf maps"]
theorem presheafHomMap.fullyFaithful_iff_isIso (F : X ⟶ Y) :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ {U : C} (x y : X.p.Fiber U), IsIso (presheafHomMap F x y) := sorry

/-- An equivalence over the base induces isomorphisms on all canonical
fiberwise Hom-presheaf maps. -/
@[stacks 02ZA "fixed-universe Hom-presheaf invariance under equivalence"]
theorem presheafHomMap.isIso_of_isEquivalence
    (F : X ⟶ Y) (hF : (toBasedFunctor F).IsEquivalence)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (presheafHomMap F x y) := sorry

/-- The canonical Hom-presheaf map of an equivalence over the base is
automatically available to typeclass search as an isomorphism. -/
@[stacks 02ZA "instance for equivalence Hom-presheaf maps"]
instance presheafHomMap.isIso
    (F : X ⟶ Y) [(toBasedFunctor F).IsEquivalence]
    {U : C} (x y : X.p.Fiber U) :
    IsIso (presheafHomMap F x y) := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
