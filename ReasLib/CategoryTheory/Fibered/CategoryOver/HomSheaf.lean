/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.StrongTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-sheaf maps of morphisms of fibred categories

When the source and target fiber pseudofunctors are prestacks, the canonical Hom-presheaf map
of a morphism of fibred categories is naturally a morphism of Hom-sheaves. This file exposes that
bundled map and the sheaf-level full-faithfulness criterion.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

namespace FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FiberedCategoryOver.{u, v, uS, vS} C}

/-- The canonical map of Hom-sheaves induced by a morphism between fibred prestacks. -/
@[stacks 04WQ "canonical fibred-category Hom-sheaf map"]
noncomputable abbrev sheafHomMap
    (F : X ⟶ Y) (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p) J]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor Y.p) J]
    {U : C} (x y : X.p.Fiber U) :
    (Functor.fiberPseudofunctor X.p).sheafHom J x y ⟶
      (Functor.fiberPseudofunctor Y.p).sheafHom J
        ((fiberFunctor F U).obj x) ((fiberFunctor F U).obj y) :=
  (strongTrans F).sheafHomMap J x y

/-- Forgetting a fibred-category Hom-sheaf map recovers its Hom-presheaf map. -/
@[simp, stacks 04WQ "fibred-category Hom-sheaf map underlying presheaf readout"]
theorem SheafMap.hom
    (F : X ⟶ Y) (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p) J]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor Y.p) J]
    {U : C} (x y : X.p.Fiber U) :
    (sheafHomMap F J x y).hom = presheafHomMap F x y := sorry

/-- The identity morphism of a fibred prestack induces the identity map of every Hom-sheaf. -/
@[simp, stacks 04WQ "identity law for fibred-category Hom-sheaf maps"]
theorem SheafMap.id
    (X : FiberedCategoryOver.{u, v, uS, vS} C) (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p) J]
    {U : C} (x y : X.p.Fiber U) :
    sheafHomMap (𝟙 X) J x y =
      𝟙 ((Functor.fiberPseudofunctor X.p).sheafHom J x y) := sorry

/-- Canonical Hom-sheaf maps preserve composition of morphisms of fibred categories. -/
@[stacks 04WQ "composition law for fibred-category Hom-sheaf maps"]
theorem SheafMap.comp
    (F : X ⟶ Y) (G : Y ⟶ Z) (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p) J]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor Y.p) J]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor Z.p) J]
    {U : C} (x y : X.p.Fiber U) :
    sheafHomMap (F ≫ G) J x y =
      sheafHomMap F J x y ≫
        sheafHomMap G J ((fiberFunctor F U).obj x) ((fiberFunctor F U).obj y) := sorry

/-- The bundled Hom-sheaf map is an isomorphism exactly when the underlying Hom-presheaf map
is an isomorphism. -/
@[stacks 04WQ "fibred-category Hom-sheaf map isomorphism readout"]
theorem SheafMap.isIso_iff
    (F : X ⟶ Y) (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p) J]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor Y.p) J]
    {U : C} (x y : X.p.Fiber U) :
    IsIso (sheafHomMap F J x y) ↔ IsIso (presheafHomMap F x y) := sorry

/-- A morphism of fibred prestacks is fully faithful exactly when all of its canonical
Hom-sheaf maps are isomorphisms. -/
@[stacks 04WQ "fibred-category full faithfulness via Hom-sheaves"]
theorem SheafMap.fullyFaithful_iff_isIso
    (F : X ⟶ Y) (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p) J]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor Y.p) J] :
    Nonempty (FiberedCategoryOver.toBasedFunctor F).FullyFaithful ↔
      ∀ {U : C} (x y : X.p.Fiber U), IsIso (sheafHomMap F J x y) := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
