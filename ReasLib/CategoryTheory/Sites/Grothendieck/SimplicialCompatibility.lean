/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialMorphism

/-!
# Compatibility of cocontinuous functors with simplicial augmentations

A morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` is compatible with a fiberwise
morphism of simplicial sites and a pair of augmentations when it is presented
by a cocontinuous functor closing the degree-zero square.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

namespace CategoryTheory.Grothendieck

section

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : F.obj (op ⦋0⦌) ⥤ D) (u0' : F'.obj (op ⦋0⦌) ⥤ D')
variable (α : F ⟶ F') (v : D ⥤ D')
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable [hα : IsFiberwiseMorphism J J' α]
variable [h_aug : IsAugmentation F J K u0] [h_aug' : IsAugmentation F' J' K' u0']
include instF instF' hα h_aug h_aug'

/-- A morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` presented by `v : D ⥤ D'` is compatible
with a fiberwise morphism `α` and augmentations `u0`, `u0'` when `v` is cocontinuous and
`(α.app (op ⦋0⦌)).toFunctor ⋙ u0' = u0 ⋙ v`. -/
class IsCompatible (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
    (K : Precoverage D) (K' : Precoverage D') (u0 : F.obj (op ⦋0⦌) ⥤ D)
    (u0' : F'.obj (op ⦋0⦌) ⥤ D') (α : F ⟶ F') (v : D ⥤ D') : Prop where
  /-- `v` is cocontinuous for the chosen target precoverages. -/
  isCocontinuous : Functor.Precoverage.IsCocontinuous v K K'
  /-- The presenting functors satisfy `u'₀ ∘ v₀ = v₋₁ ∘ u₀`. -/
  comp_eq : (α.app (op ⦋0⦌)).toFunctor ⋙ u0' = u0 ⋙ v

/-- Compatibility is selected-cover cocontinuity of `v` together with the degree-zero
functor square. -/
theorem IsCompatible.iff :
    IsCompatible J J' K K' u0 u0' α v ↔
      Functor.Precoverage.IsCocontinuous v K K' ∧
        (α.app (op ⦋0⦌)).toFunctor ⋙ u0' = u0 ⋙ v :=
  sorry

variable [h : IsCompatible J J' K K' u0 u0' α v]
include h

variable [K.IsSite] [K'.IsSite]
variable [(J (op ⦋0⦌)).IsSite] [(J' (op ⦋0⦌)).IsSite]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0.op.HasPointwiseRightKanExtension P]
variable [∀ P : (F'.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0'.op.HasPointwiseRightKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, v.op.HasPointwiseRightKanExtension P]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, (u0 ⋙ v).op.HasPointwiseRightKanExtension P]

/-- Topology-level cocontinuity of a compatible presenting functor. -/
@[reducible] def IsCompatible.isCocontinuous_topology :
    v.IsCocontinuous K.toGrothendieck K'.toGrothendieck :=
  @Functor.Precoverage.IsCocontinuous.toCocontinuousOfCoverBasis
    _ _ _ _ K K' v h.isCocontinuous
    (fun hS ↦ Precoverage.HasFactoringPullbacks.exists_generate_le (J := K') hS)

/-- The composite of an augmentation functor with a compatible presenting functor is
cocontinuous. -/
@[reducible] def IsCompatible.isCocontinuous_compFunctor :
    (u0 ⋙ v).IsCocontinuous (J (op ⦋0⦌)).toGrothendieck K'.toGrothendieck :=
  @CategoryTheory.isCocontinuous_comp _ _ _ _ _ _ u0 v
    (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck K'.toGrothendieck
    (@Functor.Precoverage.IsCocontinuous.toCocontinuousOfCoverBasis
      _ _ _ _ _ _ u0 h_aug.isCocontinuous
      (fun hS ↦ Precoverage.HasFactoringPullbacks.exists_generate_le (J := K) hS))
    (isCocontinuous_topology J J' K K' u0 u0' α v)

/-- The morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` induced by the cocontinuous functor `v`. -/
def IsCompatible.topos : MorphismOfTopoiIn K'.toGrothendieck K.toGrothendieck :=
  @Functor.morphismOfTopoiInOfCocontinuous _ _ _ _ v
    K.toGrothendieck K'.toGrothendieck
    (isCocontinuous_topology J J' K K' u0 u0' α v) _ _

/-- Inverse image of `IsCompatible.topos` is cocontinuous sheaf pullback along `v`. -/
theorem IsCompatible.topos_inverseImage :
    (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage =
      v.sheafPullbackCocontinuous (Type w) K.toGrothendieck K'.toGrothendieck :=
  sorry

/-- Inverse images of `a'₀ ∘ h₀` and `h₋₁ ∘ a₀` are canonically isomorphic as morphisms of
topoi, by composition of cocontinuous functors and uniqueness of left adjoints. -/
def IsCompatible.inverseImage_comp :
    u0'.sheafPullbackCocontinuous (Type w) (J' (op ⦋0⦌)).toGrothendieck K'.toGrothendieck ⋙
        (IsFiberwiseMorphism.topos J J' α ⦋0⦌).inverseImage ≅
      (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage ⋙
        u0.sheafPullbackCocontinuous (Type w) (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck :=
  let hu0 : u0.IsCocontinuous (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck :=
    @Functor.Precoverage.IsCocontinuous.toCocontinuousOfCoverBasis
      _ _ _ _ _ _ u0 h_aug.isCocontinuous
      (fun hS ↦ Precoverage.HasFactoringPullbacks.exists_generate_le (J := K) hS)
  let hu0' : u0'.IsCocontinuous (J' (op ⦋0⦌)).toGrothendieck K'.toGrothendieck :=
    @Functor.Precoverage.IsCocontinuous.toCocontinuousOfCoverBasis
      _ _ _ _ _ _ u0' h_aug'.isCocontinuous
      (fun hS ↦ Precoverage.HasFactoringPullbacks.exists_generate_le (J := K') hS)
  let hv := isCocontinuous_topology J J' K K' u0 u0' α v
  let huv := isCocontinuous_compFunctor J J' K K' u0 u0' α v
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        (@Functor.sheafPullbackCocontinuousAdjunction _ _ _ _ u0'
          (J' (op ⦋0⦌)).toGrothendieck K'.toGrothendieck hu0' _ _)
        ((α.app (op ⦋0⦌)).toFunctor.sheafPullbackCocontinuousAdjunction
          (J (op ⦋0⦌)).toGrothendieck (J' (op ⦋0⦌)).toGrothendieck)).ofNatIsoRight
      (@Functor.sheafPushforwardCocontinuousComp' _ _ _ _ _ _
          (J (op ⦋0⦌)).toGrothendieck (J' (op ⦋0⦌)).toGrothendieck K'.toGrothendieck
          (α.app (op ⦋0⦌)).toFunctor u0' _ hu0' (Type w) _ _ _
          (u0 ⋙ v) (eqToIso h.comp_eq) huv _ ≪≫
        (@Functor.sheafPushforwardCocontinuousComp' _ _ _ _ _ _
          (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck K'.toGrothendieck
          u0 v hu0 hv (Type w) _ _ _ (u0 ⋙ v) (Iso.refl _) huv _).symm))
    (Adjunction.comp
      (@Functor.sheafPullbackCocontinuousAdjunction _ _ _ _ v
        K.toGrothendieck K'.toGrothendieck hv _ _)
      (@Functor.sheafPullbackCocontinuousAdjunction _ _ _ _ u0
        (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck hu0 _ _))

end

/-- The identity functor is compatible with the identity morphism of fiberwise simplicial
sites and equal augmentations. -/
instance IsCompatible.id {F : SimplicialObject Cat.{v, u}}
    (J : ∀ n, Precoverage (F.obj n)) {D : Type u} [Category.{v} D] (K : Precoverage D)
    (u0 : F.obj (op ⦋0⦌) ⥤ D)
    [IsFiberwiseSite F J] [IsFiberwiseMorphism J J (𝟙 F)] [IsAugmentation F J K u0] :
    IsCompatible J J K K u0 u0 (𝟙 F) (𝟭 D) :=
  sorry

end CategoryTheory.Grothendieck
