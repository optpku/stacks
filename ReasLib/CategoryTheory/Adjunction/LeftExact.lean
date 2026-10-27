/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Left-exact adjunctions

A `LeftExactAdjunction C D` bundles a left-exact functor `D ⥤ C` (the "inverse image")
together with its right adjoint (the "direct image / pushforward") and the adjunction datum.
This is the categorical core of a geometric morphism between sites or topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

/-- A bundled left-exact adjunction: a left-exact functor `D ⥤ C` equipped with a chosen
right adjoint and the adjunction datum. This is the categorical core of a geometric morphism. -/
structure LeftExactAdjunction (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] where
  /-- The left-exact inverse image functor. -/
  inverseImageFunctor : D ⥤ₗ C
  /-- The direct image (right adjoint) functor. -/
  pushforward : C ⥤ D
  /-- The adjunction `inverseImage ⊣ pushforward`. -/
  adjunction : inverseImageFunctor.obj ⊣ pushforward

namespace LeftExactAdjunction

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/-- The underlying inverse image functor of a left-exact adjunction. -/
abbrev inverseImage (f : LeftExactAdjunction A B) : B ⥤ A := f.inverseImageFunctor.obj

/-- The chosen adjunction exhibits the inverse image as a left adjoint. -/
theorem inverseImageIsLeftAdjoint (f : LeftExactAdjunction A B) :
    f.inverseImage.IsLeftAdjoint :=
  f.adjunction.isLeftAdjoint

/-- The inverse image preserves finite limits. -/
theorem inverseImagePreservesFiniteLimits (f : LeftExactAdjunction A B) :
    PreservesFiniteLimits f.inverseImage :=
  f.inverseImageFunctor.property

/-- The direct image of a left-exact adjunction preserves finite products, as every right
adjoint preserves limits. -/
theorem pushforwardPreservesFiniteProducts (f : LeftExactAdjunction A B) :
    PreservesFiniteProducts f.pushforward where
  preserves _ := f.adjunction.rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- A left-exact inverse image carries any chosen terminal object to a terminal
object, hence to any chosen terminal object of its target. -/
noncomputable def inverseImageTerminalIso
    (f : LeftExactAdjunction A B) {X : B} (hX : IsTerminal X)
    {Y : A} (hY : IsTerminal Y) : f.inverseImage.obj X ≅ Y :=
  IsTerminal.uniqueUpToIso
    (@IsTerminal.isTerminalObj B _ A _ f.inverseImage X
      (((inverseImagePreservesFiniteLimits f).preservesFiniteLimits _).preservesLimit) hX)
    hY

/-- The identity left-exact adjunction. -/
def id (C : Type u₁) [Category.{v₁} C] : LeftExactAdjunction C C where
  inverseImageFunctor :=
    ⟨𝟭 C, (inferInstance : PreservesFiniteLimits (𝟭 C))⟩
  pushforward := 𝟭 C
  adjunction := Adjunction.id

/-- Composition of left-exact adjunctions. -/
abbrev comp (f : LeftExactAdjunction B C) (g : LeftExactAdjunction A B) :
    LeftExactAdjunction A C where
  inverseImageFunctor :=
    ⟨f.inverseImageFunctor.obj ⋙ g.inverseImageFunctor.obj,
      comp_preservesFiniteLimits f.inverseImageFunctor.obj g.inverseImageFunctor.obj⟩
  pushforward := g.pushforward ⋙ f.pushforward
  adjunction := f.adjunction.comp g.adjunction

/-- The inverse-image functor of the identity left-exact adjunction is canonically the
identity functor.  This is explicit isomorphism data, not transport through an equality. -/
def idInverseImageIso :
    (LeftExactAdjunction.id C).inverseImage ≅ 𝟭 C :=
  Iso.refl _

/-- The inverse-image functor of a composite left-exact adjunction is canonically the
composite of the inverse-image functors.  This is explicit isomorphism data. -/
def compInverseImageIso (f : LeftExactAdjunction B C) (g : LeftExactAdjunction A B) :
    (f.comp g).inverseImage ≅ f.inverseImage ⋙ g.inverseImage :=
  Iso.refl _

/-- The identity left-exact adjunction has the identity inverse image. -/
@[simp] theorem id_inverseImage :
    (LeftExactAdjunction.id C).inverseImage = 𝟭 C := rfl

/-- The identity left-exact adjunction has the identity pushforward. -/
@[simp] theorem id_pushforward :
    (LeftExactAdjunction.id C).pushforward = 𝟭 C := rfl

/-- The inverse image of a composite is the composite of the inverse images. -/
@[simp] theorem comp_inverseImage (f : LeftExactAdjunction B C) (g : LeftExactAdjunction A B) :
    (f.comp g).inverseImage = f.inverseImage ⋙ g.inverseImage := rfl

/-- The pushforward of a composite is the reverse composite of the pushforwards. -/
@[simp] theorem comp_pushforward (f : LeftExactAdjunction B C) (g : LeftExactAdjunction A B) :
    (f.comp g).pushforward = g.pushforward ⋙ f.pushforward := rfl

/-- A left-exact adjunction is an embedding when the pushforward is fully faithful. -/
class IsEmbedding (f : LeftExactAdjunction A B) : Prop extends
    f.pushforward.Full, f.pushforward.Faithful

namespace IsEmbedding

variable (f : LeftExactAdjunction A B) [IsEmbedding f]

/-- The pushforward of an embedding is fully faithful. -/
noncomputable def pushforwardFullyFaithful : f.pushforward.FullyFaithful :=
  .ofFullyFaithful f.pushforward

/-- The counit of an embedding is an isomorphism. -/
theorem counit_isIso : IsIso f.adjunction.counit := sorry

/-- The pushforward of an embedding reflects monomorphisms. -/
theorem pushforwardReflectsMonomorphisms : f.pushforward.ReflectsMonomorphisms := sorry

/-- The pushforward of an embedding reflects epimorphisms. -/
theorem pushforwardReflectsEpimorphisms : f.pushforward.ReflectsEpimorphisms := sorry

/-- The pushforward of an embedding reflects isomorphisms. -/
theorem pushforwardReflectsIsomorphisms : f.pushforward.ReflectsIsomorphisms := sorry

end IsEmbedding

/-! ### Localization on slice categories -/

/-- The left-exact adjunction on slice categories induced by `f` at `Y`. Its inverse image is
postcomposition by `f.inverseImage`; its direct image is the canonical pullback-after-postcomposition
right adjoint. -/
@[stacks 04IF "slice adjunction"]
noncomputable def localization [HasPullbacks B] (f : LeftExactAdjunction A B) (Y : B) :
    LeftExactAdjunction (Over (f.inverseImage.obj Y)) (Over Y) where
  inverseImageFunctor :=
    ⟨Over.post f.inverseImage,
      PreservesFiniteLimits.overPost⟩
  pushforward := Over.post f.pushforward ⋙ Over.pullback (f.adjunction.unit.app Y)
  adjunction := Over.postAdjunctionLeft f.adjunction

/-- The inverse image of `f.localization Y` sends a map `Z ⟶ Y` to the map
`f.inverseImage.obj Z ⟶ f.inverseImage.obj Y`. -/
@[stacks 04IF "inverse image", simp]
theorem localization_inverseImage_obj [HasPullbacks B]
    (f : LeftExactAdjunction A B) (Y : B) (Z : Over Y) :
    (f.localization Y).inverseImage.obj Z = Over.mk (f.inverseImage.map Z.hom) := sorry

/-- Restricting to `f.inverseImage.obj Y` and then applying the localized pushforward is
canonically isomorphic to applying `f.pushforward` and then restricting to `Y`. -/
@[stacks 04IF "direct image"]
noncomputable def localization_pushforwardStarIso
    [HasBinaryProducts A] [HasPullbacks B] [HasBinaryProducts B]
    (f : LeftExactAdjunction A B) (Y : B) :
    Over.star (f.inverseImage.obj Y) ⋙ (f.localization Y).pushforward ≅
      f.pushforward ⋙ Over.star Y :=
  let localizedAdj :
      Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ⊣
        Over.star (f.inverseImage.obj Y) ⋙ (f.localization Y).pushforward :=
    (Over.postAdjunctionLeft f.adjunction).comp (Over.forgetAdjStar (f.inverseImage.obj Y))
  let globalAdj :
      Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ⊣
        f.pushforward ⋙ Over.star Y :=
    ((Over.forgetAdjStar Y).comp f.adjunction).ofNatIsoLeft
      (eqToIso (Over.post_forget_eq_forget_comp f.inverseImage Y) :
        Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ≅
          Over.forget Y ⋙ f.inverseImage)
  Adjunction.rightAdjointUniq localizedAdj globalAdj


end LeftExactAdjunction

end CategoryTheory
