/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.Simplicial.Morphism

/-!
# Compatibility of morphisms of sites with simplicial augmentations

A morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` is compatible with a morphism of
simplicial sites and a pair of augmentations when it is presented by an exact
morphism of sites whose presenting functor closes the degree-zero square.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SimplicialSites

section

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : D ⥤ C.obj ⦋0⦌) (u0' : D' ⥤ C'.obj ⦋0⦌)
variable (α : C' ⟶ C) (v : D' ⥤ D)
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, u0'.op.HasLeftKanExtension P]
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension P]
variable [instC : IsMorphismDiagram C J] [instC' : IsMorphismDiagram C' J']
variable [hα : IsMorphism J J' α]
variable [h_aug : IsAugmentation C J K u0] [h_aug' : IsAugmentation C' J' K' u0']
include instC instC' hα h_aug h_aug'

/-- A morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` presented by `v : D' ⥤ D` is compatible
with a morphism of simplicial sites `α` and augmentations `u0`, `u0'` when `v` is an
exact morphism of sites and `u0' ⋙ (α.app ⦋0⦌).toFunctor = v ⋙ u0`. -/
class IsCompatible (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
    (K : Precoverage D) (K' : Precoverage D') (u0 : D ⥤ C.obj ⦋0⦌)
    (u0' : D' ⥤ C'.obj ⦋0⦌) (α : C' ⟶ C) (v : D' ⥤ D)
    [HasWeakSheafify K.toGrothendieck (Type w)]
    [∀ P : D'ᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension P] : Prop where
  /-- `v` presents a morphism of sites `D ⟶ D'`. -/
  isExact : IsExactMorphismOfSites K'.toGrothendieck K.toGrothendieck v
  /-- The presenting functors satisfy `a'₀ ∘ h₀ = h₋₁ ∘ a₀` as morphisms of sites. -/
  comp_eq : u0' ⋙ (α.app ⦋0⦌).toFunctor = v ⋙ u0

/-- Compatibility is exactness of `v` together with the degree-zero presenting-functor square. -/
theorem IsCompatible.iff :
    IsCompatible J J' K K' u0 u0' α v ↔
      IsExactMorphismOfSites K'.toGrothendieck K.toGrothendieck v ∧
        u0' ⋙ (α.app ⦋0⦌).toFunctor = v ⋙ u0 :=
  sorry

variable [h : IsCompatible J J' K K' u0 u0' α v]
include h

/-- The morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` presented by `v`. -/
def IsCompatible.topos : MorphismOfTopoiIn K'.toGrothendieck K.toGrothendieck :=
  @Functor.morphismOfTopoiInOfContinuous _ _ _ _ v
    K'.toGrothendieck K.toGrothendieck h.isExact.toIsContinuous _ _
    h.isExact.preservesFiniteLimits_sheafPullback

/-- Inverse image of `IsCompatible.topos` is sheaf pullback along `v`. -/
theorem IsCompatible.topos_inverseImage :
    (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage =
      @Functor.sheafPullback _ _ _ _ v (Type w) _ K'.toGrothendieck K.toGrothendieck
        h.isExact.toIsContinuous _ :=
  sorry

/-- Inverse images of `a'₀ ∘ h₀` and `h₋₁ ∘ a₀` are canonically isomorphic as morphisms of
topoi, by the comparison associated to their commutative square of continuous functors. -/
def IsCompatible.inverseImage_comp :
    u0'.sheafPullback (Type w) K'.toGrothendieck (J' ⦋0⦌).toGrothendieck ⋙
        (IsMorphism.topos J J' α ⦋0⦌).inverseImage ≅
      (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage ⋙
        u0.sheafPullback (Type w) K.toGrothendieck (J ⦋0⦌).toGrothendieck :=
  @Functor.ContinuousSquare.pullbackIso _ _ _ _ _ _ _ _
    _ _ _ _ u0' u0 (α.app ⦋0⦌).toFunctor v
    _ _ h.isExact.toIsContinuous _ (Type w) _ _ _ _ _ _ _ _ h.comp_eq.symm

end

/-- The identity functor is compatible with the identity morphism of simplicial sites and
equal augmentations. -/
instance IsCompatible.id {C : SimplexCategory ⥤ Cat.{v, u}}
    (J : ∀ n, Precoverage (C.obj n)) {D : Type u} [Category.{v} D] (K : Precoverage D)
    (u0 : D ⥤ C.obj ⦋0⦌)
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [HasWeakSheafify K.toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
        ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
    [∀ P : Dᵒᵖ ⥤ Type w, (𝟭 D).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J] [IsMorphism J J (𝟙 C)] [IsAugmentation C J K u0] :
    IsCompatible J J K K u0 u0 (𝟙 C) (𝟭 D) :=
  sorry

end CategoryTheory.SimplicialSites
