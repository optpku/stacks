/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coaugmenting canonical monad resolutions

The canonical unit coaugmentation is bundled with the cosimplicial resolution, functorial in the
monad, and compatible with the canonical comparison from every realization. This leaf is the
stable owner for structure transport on augmented resolutions.
-/

@[expose] public section

open CategoryTheory.CosimplicialObject
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u v₁ u₁

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Monad

variable (T : Monad C)

/-- The canonical coaugmentation of the cosimplicial resolution of a monad. -/
@[stacks 0G5N "monad resolution coaugmentation"]
noncomputable def cosimplicialResolution.coaugmentation :
    (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ T.cosimplicialResolution :=
  EndofunctorResolution.CosimplicialRealization.coaugmentation
    (cosimplicialResolution.realization T)

/-- The canonical monad-resolution coaugmentation is the unit in degree zero. -/
@[simp, stacks 0G5N "degree-zero component of the monad resolution coaugmentation"]
theorem cosimplicialResolution.coaugmentation.app_zero :
    (cosimplicialResolution.coaugmentation T).app ⦋0⦌ = T.η := sorry

/-- The canonical augmented cosimplicial object belonging to a monad resolution. -/
@[stacks 0G5N "augmented monad cosimplicial resolution"]
noncomputable def cosimplicialResolution.augmented :
    CosimplicialObject.Augmented (C ⥤ C) :=
  EndofunctorResolution.CosimplicialRealization.augmented
    (cosimplicialResolution.realization T)

/-- The point of the canonical augmented monad resolution is the identity endofunctor. -/
@[simp, stacks 0G5N "point of the augmented monad resolution"]
theorem cosimplicialResolution.augmented.left :
    (cosimplicialResolution.augmented T).left = 𝟭 C := sorry

/-- The cosimplicial component of the augmented monad resolution is its resolution. -/
@[simp, stacks 0G5N "cosimplicial component of the augmented monad resolution"]
theorem cosimplicialResolution.augmented.right :
    (cosimplicialResolution.augmented T).right = T.cosimplicialResolution := sorry

/-- The map of the augmented monad resolution is its canonical coaugmentation. -/
@[simp, stacks 0G5N "map of the augmented monad resolution"]
theorem cosimplicialResolution.augmented.hom :
    (cosimplicialResolution.augmented T).hom =
      cosimplicialResolution.coaugmentation T := sorry

variable {T : Monad C}

/-- The canonical realization isomorphism commutes with the unit-induced coaugmentations. -/
@[stacks 0G5N "coaugmentation compatibility of the canonical realization isomorphism"]
theorem Realizes.augmentedIso.w {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) :
    (CosimplicialObject.const (C ⥤ C)).map (𝟙 (𝟭 C)) ≫
        (cosimplicialResolution.augmented T).hom =
      hU.augmented.hom ≫ (Realizes.iso hU).hom := sorry

/-- A realization, together with its unit-induced coaugmentation, is canonically isomorphic to
the augmented cosimplicial resolution of the monad. -/
@[stacks 0G5N "canonical augmented isomorphism for a monad realization"]
noncomputable def Realizes.augmentedIso {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) :
    hU.augmented ≅ cosimplicialResolution.augmented T :=
  Comma.isoMk (Iso.refl (𝟭 C)) (Realizes.iso hU)
    (Realizes.augmentedIso.w hU)

/-- Map the canonical augmented realization isomorphism through an arbitrary functor. This is
the stable comparison owner for downstream transports on augmented cosimplicial resolutions. -/
@[stacks 0G5N "functorial image of the augmented cosimplicial realization isomorphism"]
noncomputable def Realizes.augmentedIso.map
    {D : Type u₁} [Category.{v₁} D] {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U)
    (F : CosimplicialObject.Augmented (C ⥤ C) ⥤ D) :
    F.obj hU.augmented ≅ F.obj (cosimplicialResolution.augmented T) :=
  F.mapIso (Realizes.augmentedIso hU)

/-- The forward point component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "point component of the augmented cosimplicial realization isomorphism"]
theorem Realizes.augmentedIso.hom_left {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) :
    (Realizes.augmentedIso hU).hom.left = 𝟙 (𝟭 C) := sorry

/-- The forward cosimplicial component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "cosimplicial component of the augmented realization isomorphism"]
theorem Realizes.augmentedIso.hom_right {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) :
    (Realizes.augmentedIso hU).hom.right = (Realizes.iso hU).hom := sorry

/-- The inverse point component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "inverse point component of the augmented cosimplicial realization isomorphism"]
theorem Realizes.augmentedIso.inv_left {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) :
    (Realizes.augmentedIso hU).inv.left = 𝟙 (𝟭 C) := sorry

/-- The inverse cosimplicial component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "inverse cosimplicial component of the augmented realization isomorphism"]
theorem Realizes.augmentedIso.inv_right {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) :
    (Realizes.augmentedIso hU).inv.right = (Realizes.iso hU).inv := sorry

/-- A monad morphism's resolution map commutes with canonical coaugmentations. -/
@[stacks 0G5N "coaugmentation compatibility of a monad resolution map"]
theorem cosimplicialResolution.augmentedMap.w {T S : Monad C} (alpha : T ⟶ S) :
    (CosimplicialObject.const (C ⥤ C)).map (𝟙 (𝟭 C)) ≫
        (cosimplicialResolution.augmented S).hom =
      (cosimplicialResolution.augmented T).hom ≫
        cosimplicialResolution.hom alpha := sorry

/-- The morphism of augmented cosimplicial resolutions induced by a monad morphism. -/
@[stacks 0G5N "morphism of augmented monad resolutions"]
noncomputable def cosimplicialResolution.augmentedMap {T S : Monad C} (alpha : T ⟶ S) :
    cosimplicialResolution.augmented T ⟶ cosimplicialResolution.augmented S where
  left := 𝟙 (𝟭 C)
  right := cosimplicialResolution.hom alpha
  w := cosimplicialResolution.augmentedMap.w alpha

/-- The point component of an augmented monad resolution map is the identity. -/
@[simp]
theorem cosimplicialResolution.augmentedMap.left {T S : Monad C} (alpha : T ⟶ S) :
    (cosimplicialResolution.augmentedMap alpha).left = 𝟙 (𝟭 C) := sorry

/-- The cosimplicial component of an augmented monad resolution map is the resolution map. -/
@[simp]
theorem cosimplicialResolution.augmentedMap.right {T S : Monad C} (alpha : T ⟶ S) :
    (cosimplicialResolution.augmentedMap alpha).right =
      cosimplicialResolution.hom alpha := sorry

/-- The identity monad morphism induces the identity augmented resolution map. -/
@[simp]
theorem cosimplicialResolution.augmentedMap.id (T : Monad C) :
    cosimplicialResolution.augmentedMap (𝟙 T) =
      𝟙 (cosimplicialResolution.augmented T) := sorry

/-- Augmented monad resolution maps preserve composition. -/
@[simp]
theorem cosimplicialResolution.augmentedMap.comp {T S R : Monad C}
    (alpha : T ⟶ S) (beta : S ⟶ R) :
    cosimplicialResolution.augmentedMap (alpha ≫ beta) =
      cosimplicialResolution.augmentedMap alpha ≫
        cosimplicialResolution.augmentedMap beta := sorry

/-- The augmented cosimplicial resolution as a functor of the monad. -/
@[stacks 0G5N "functorial augmented monad resolution"]
noncomputable def cosimplicialResolution.augmentedFunctor :
    Monad C ⥤ CosimplicialObject.Augmented (C ⥤ C) where
  obj T := cosimplicialResolution.augmented T
  map alpha := cosimplicialResolution.augmentedMap alpha
  map_id := cosimplicialResolution.augmentedMap.id
  map_comp := cosimplicialResolution.augmentedMap.comp

end Monad

namespace EndofunctorResolution.toMonad

/-- Bundling the raw cosimplicial resolution with its unit coaugmentation agrees with the
canonical augmented resolution of the generated monad. -/
@[stacks 0G5N "raw augmented cosimplicial resolution agrees with the generated monad resolution"]
theorem augmented_eq {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0) :
    Monad.cosimplicialResolution.augmented
        (EndofunctorResolution.toMonad d s hδσ₀ hδσ₁ hσσ) =
      EndofunctorResolution.CosimplicialRealization.augmented
        (EndofunctorResolution.cosimplicial.resolution.realization
          d s hδσ₀ hδσ₁ hσσ) := sorry

end EndofunctorResolution.toMonad

end CategoryTheory
