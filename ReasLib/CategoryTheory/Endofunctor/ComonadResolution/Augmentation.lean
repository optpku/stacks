/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0G5N

# Augmenting canonical comonad resolutions

The canonical counit augmentation is bundled with the simplicial resolution, functorial in the
comonad, and compatible with the canonical comparison from every realization. This leaf is the
stable owner for structure transport on augmented resolutions.
-/

@[expose] public section

open Opposite
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmentation
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Comonad

variable (G : Comonad C)

/-- The canonical augmentation of the simplicial resolution of a comonad. -/
@[stacks 0G5N "comonad resolution augmentation"]
noncomputable def simplicialResolution.augmentation :
    G.simplicialResolution ⟶ (const (C ⥤ C)).obj (𝟭 C) :=
  EndofunctorResolution.Realization.augmentation (simplicialResolution.realization G)

/-- The canonical comonad-resolution augmentation is the counit in degree zero. -/
@[simp, stacks 0G5N "degree-zero component of the comonad resolution augmentation"]
theorem simplicialResolution.augmentation.app_zero :
    (simplicialResolution.augmentation G).app (op ⦋0⦌) = G.ε := sorry

/-- The canonical augmented simplicial object belonging to a comonad resolution.  Keeping the
augmentation and its point bundled makes evaluation and whiskering compositional for downstream
constructions. -/
@[stacks 0G5N "augmented comonad resolution"]
noncomputable def simplicialResolution.augmented :
    SimplicialObject.Augmented (C ⥤ C) :=
  EndofunctorResolution.Realization.augmented (simplicialResolution.realization G)

/-- The left component of the canonical augmented resolution is the simplicial resolution. -/
@[simp, stacks 0G5N "simplicial component of the augmented comonad resolution"]
theorem simplicialResolution.augmented.left :
    (simplicialResolution.augmented G).left = G.simplicialResolution := sorry

/-- The point of the canonical augmented resolution is the identity endofunctor. -/
@[simp, stacks 0G5N "point of the augmented comonad resolution"]
theorem simplicialResolution.augmented.right :
    (simplicialResolution.augmented G).right = 𝟭 C := sorry

/-- The map of the canonical augmented resolution is the canonical augmentation. -/
@[simp, stacks 0G5N "map of the augmented comonad resolution"]
theorem simplicialResolution.augmented.hom :
    (simplicialResolution.augmented G).hom =
      simplicialResolution.augmentation G := sorry

variable {G : Comonad C}

/-- The canonical realization isomorphism commutes with the counit-induced augmentations. -/
@[stacks 0G5N "augmentation compatibility of the canonical realization isomorphism"]
theorem Realizes.augmentedIso.w {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) :
    (Realizes.iso hU).hom ≫ (simplicialResolution.augmented G).hom =
      hU.augmented.hom ≫
        (SimplicialObject.const (C ⥤ C)).map (𝟙 (𝟭 C)) := sorry

/-- A realization, together with its counit-induced augmentation, is canonically isomorphic to
the augmented simplicial resolution of the comonad. -/
@[stacks 0G5N "canonical augmented isomorphism for a comonad realization"]
noncomputable def Realizes.augmentedIso {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) :
    hU.augmented ≅ simplicialResolution.augmented G :=
  Comma.isoMk (Realizes.iso hU) (Iso.refl (𝟭 C))
    (Realizes.augmentedIso.w hU)

/-- Map the canonical augmented realization isomorphism through an arbitrary functor.  This is
the stable comparison owner for downstream transports of structure on augmented resolutions. -/
@[stacks 0G5N "functorial image of the augmented realization isomorphism"]
noncomputable def Realizes.augmentedIso.map
    {D : Type u'} [Category.{v'} D] {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U)
    (F : SimplicialObject.Augmented (C ⥤ C) ⥤ D) :
    F.obj hU.augmented ≅ F.obj (simplicialResolution.augmented G) :=
  F.mapIso (Realizes.augmentedIso hU)

/-- The forward simplicial component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "simplicial component of the augmented realization isomorphism"]
theorem Realizes.augmentedIso.hom_left {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) :
    (Realizes.augmentedIso hU).hom.left = (Realizes.iso hU).hom := sorry

/-- The forward point component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "point component of the augmented realization isomorphism"]
theorem Realizes.augmentedIso.hom_right {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) :
    (Realizes.augmentedIso hU).hom.right = 𝟙 (𝟭 C) := sorry

/-- The inverse simplicial component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "inverse simplicial component of the augmented realization isomorphism"]
theorem Realizes.augmentedIso.inv_left {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) :
    (Realizes.augmentedIso hU).inv.left = (Realizes.iso hU).inv := sorry

/-- The inverse point component of the canonical augmented realization isomorphism. -/
@[simp, stacks 0G5N "inverse point component of the augmented realization isomorphism"]
theorem Realizes.augmentedIso.inv_right {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) :
    (Realizes.augmentedIso hU).inv.right = 𝟙 (𝟭 C) := sorry

/-- A comonad morphism's resolution map commutes with the canonical augmentations. -/
@[stacks 0G5N "augmentation compatibility of a comonad resolution map"]
theorem simplicialResolution.augmentedMap.w {G H : Comonad C} (α : G ⟶ H) :
    simplicialResolution.hom α ≫ (simplicialResolution.augmented H).hom =
      (simplicialResolution.augmented G).hom ≫
        (SimplicialObject.const (C ⥤ C)).map (𝟙 (𝟭 C)) := sorry

/-- The morphism of augmented simplicial resolutions induced by a comonad morphism. -/
@[stacks 0G5N "morphism of augmented comonad resolutions"]
noncomputable def simplicialResolution.augmentedMap {G H : Comonad C}
    (α : G ⟶ H) :
    simplicialResolution.augmented G ⟶ simplicialResolution.augmented H where
  left := simplicialResolution.hom α
  right := 𝟙 (𝟭 C)
  w := simplicialResolution.augmentedMap.w α

/-- The left component of an augmented resolution map is the simplicial resolution map. -/
@[simp, stacks 0G5N "left component of an augmented comonad resolution map"]
theorem simplicialResolution.augmentedMap.left {G H : Comonad C} (α : G ⟶ H) :
    (simplicialResolution.augmentedMap α).left = simplicialResolution.hom α := sorry

/-- The point component of an augmented resolution map is the identity. -/
@[simp, stacks 0G5N "point component of an augmented comonad resolution map"]
theorem simplicialResolution.augmentedMap.right {G H : Comonad C} (α : G ⟶ H) :
    (simplicialResolution.augmentedMap α).right = 𝟙 (𝟭 C) := sorry

/-- The identity comonad morphism induces the identity augmented resolution map. -/
@[simp, stacks 0G5N "identity augmented comonad resolution map"]
theorem simplicialResolution.augmentedMap.id (G : Comonad C) :
    simplicialResolution.augmentedMap (𝟙 G) =
      𝟙 (simplicialResolution.augmented G) := sorry

/-- Augmented resolution maps preserve composition of comonad morphisms. -/
@[simp, stacks 0G5N "composition of augmented comonad resolution maps"]
theorem simplicialResolution.augmentedMap.comp {G H K : Comonad C}
    (α : G ⟶ H) (β : H ⟶ K) :
    simplicialResolution.augmentedMap (α ≫ β) =
      simplicialResolution.augmentedMap α ≫
        simplicialResolution.augmentedMap β := sorry

/-- The canonical augmented simplicial resolution as a functor of the comonad. -/
@[stacks 0G5N "functorial augmented comonad resolution"]
noncomputable def simplicialResolution.augmentedFunctor :
    Comonad C ⥤ SimplicialObject.Augmented (C ⥤ C) where
  obj G := simplicialResolution.augmented G
  map α := simplicialResolution.augmentedMap α
  map_id := simplicialResolution.augmentedMap.id
  map_comp := simplicialResolution.augmentedMap.comp

end Comonad

namespace EndofunctorResolution.toComonad

/-- Bundling the raw resolution with its counit augmentation agrees with the canonical
augmented resolution of the generated comonad. -/
@[stacks 0G5N "raw augmented resolution agrees with the generated comonad resolution"]
theorem augmented_eq {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 1) :
    Comonad.simplicialResolution.augmented
        (EndofunctorResolution.toComonad d s hσδ₀ hσδ₁ hσσ) =
      EndofunctorResolution.Realization.augmented
        (EndofunctorResolution.simplicial.resolution.realization
          d s hσδ₀ hσδ₁ hσσ) := sorry

end EndofunctorResolution.toComonad

end CategoryTheory
