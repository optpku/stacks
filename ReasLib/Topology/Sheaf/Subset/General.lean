/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.Sheaves.Stalks.Filtered
public import ReasLib.Topology.Sheaves.Stalks.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaves on arbitrary subsets: pushforward is fully faithful

For any subset `Z ⊆ X`, the pushforward along the subset inclusion `Z ↪ X` establishes a
fully faithful embedding of sheaves on the subspace into sheaves on the ambient space.

A morphism of pushforwards is recovered on an open `W ⊆ Z` from its component on the largest
open of `X` with trace `W`; this gives the explicit preimage of full faithfulness. The inverse of
the pullback-pushforward counit is the preimage of the unit at a pushforward.

## Main declarations

- `TopCat.Sheaf.Subset.pushforwardPreimage`: explicit preimage along the hull of an open of `Z`
- `TopCat.Sheaf.Subset.fullyFaithful`: pushforward is fully faithful
- `TopCat.Sheaf.Subset.counitInv`: explicit inverse of the counit
- `TopCat.Sheaf.Subset.counit_isIso`: the counit is an isomorphism
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open scoped TopCat

noncomputable section

universe v w

namespace TopCat.Sheaf.Subset

variable {X : TopCat.{v}}
variable {C : Type w} [Category.{v} C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- The largest open subset of `X` whose trace on `Z` is a given open subset `W` of `Z`.
This is mathlib's right adjoint `Topology.IsInducing.functor` to restriction of opens. -/
abbrev hull (Z : Set X) (W : Opens (TopCat.subsetSpace Z)) : Opens X :=
  (TopCat.subsetInclusion_isInducing Z).functorObj W

/-- The trace on `Z` of the hull of `W` is `W` itself. -/
theorem map_hull (Z : Set X) (W : Opens (TopCat.subsetSpace Z)) :
    (Opens.map (TopCat.subsetInclusion Z)).obj (hull Z W) = W :=
  (TopCat.subsetInclusion_isInducing Z).map_functorObj W

/-- Every open subset of `X` is contained in the hull of its trace on `Z`. -/
theorem le_hull_map (Z : Set X) (V : Opens X) :
    V ≤ hull Z ((Opens.map (TopCat.subsetInclusion Z)).obj V) :=
  (TopCat.subsetInclusion_isInducing Z).le_functorObj_iff.mpr le_rfl

/-- The explicit preimage of a morphism of pushforwards along a subset inclusion: on an open
`W ⊆ Z` it is the component of the given morphism on the hull of `W`, transported along
`map_hull`. -/
@[stacks 00AE "explicit preimage for subset pushforward"]
noncomputable def pushforwardPreimage (Z : Set X)
    {F G : TopCat.Sheaf C (TopCat.subsetSpace Z)}
    (φ : (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).obj F ⟶
      (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).obj G) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun W ↦
        F.obj.map (eqToHom (congrArg op (map_hull Z W.unop).symm)) ≫
          φ.hom.app (op (hull Z W.unop)) ≫
            G.obj.map (eqToHom (congrArg op (map_hull Z W.unop)))
      naturality := sorry }

/-- Pushforward along a subset inclusion is fully faithful, with explicit preimage
`pushforwardPreimage`. -/
@[stacks 00AE "subset pushforward is fully faithful", stacks 01AX "(2)"]
noncomputable def fullyFaithful (Z : Set X) :
    (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).FullyFaithful where
  preimage φ := pushforwardPreimage Z φ
  map_preimage := sorry
  preimage_map := sorry

/-- The explicit inverse of the pullback-pushforward counit along a subset inclusion: the
preimage under the fully faithful pushforward of the unit at `i_* G`. -/
@[stacks 00AE "inverse of the subset pullback-pushforward counit"]
noncomputable def counitInv (Z : Set X) (G : TopCat.Sheaf C (TopCat.subsetSpace Z)) :
    G ⟶ (TopCat.Sheaf.pullback C (TopCat.subsetInclusion Z)).obj
      ((TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).obj G) :=
  (fullyFaithful Z).preimage
    ((TopCat.Sheaf.pullbackPushforwardAdjunction C (TopCat.subsetInclusion Z)).unit.app
      ((TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).obj G))

/-- The counit followed by its explicit inverse is the identity. -/
@[reassoc (attr := simp)]
theorem counit_app_counitInv (Z : Set X) (G : TopCat.Sheaf C (TopCat.subsetSpace Z)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction C (TopCat.subsetInclusion Z)).counit.app G ≫
      counitInv Z G = 𝟙 _ := sorry

/-- The explicit inverse followed by the counit is the identity. -/
@[reassoc (attr := simp)]
theorem counitInv_counit_app (Z : Set X) (G : TopCat.Sheaf C (TopCat.subsetSpace Z)) :
    counitInv Z G ≫
      (TopCat.Sheaf.pullbackPushforwardAdjunction C (TopCat.subsetInclusion Z)).counit.app G =
        𝟙 _ := sorry

/-- The counit of the pullback-pushforward adjunction along a subset inclusion is an
isomorphism, with explicit componentwise inverse `counitInv`. -/
@[stacks 00AE "pullback-pushforward counit is an isomorphism for subset inclusions",
  stacks 01AX "(4)"]
instance counit_isIso (Z : Set X) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction C
      (TopCat.subsetInclusion Z)).counit :=
  ⟨⟨{ app := counitInv Z, naturality := sorry }, sorry, sorry⟩⟩

/-- Pushforward along a subset inclusion induces a bijection on every hom set.

This is the pointwise form of `fullyFaithful`, kept separate for consumers that work directly
with morphism functions. -/
theorem map_bijective (Z : Set X) (F G : TopCat.Sheaf C (TopCat.subsetSpace Z)) :
    Function.Bijective (fun (η : F ⟶ G) ↦
      (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).map η) := sorry

end TopCat.Sheaf.Subset

end

end
