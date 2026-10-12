/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Remark_85_4_1_Fiberwise
public import stacks_project.Chap85.Remark_85_5_1_Morphism

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
  -- Local instance justification (search instability): Precoverage.IsCocontinuous is a field of IsCompatible, whose extra J/α/u0 parameters cannot be synthesized from v.
  letI : Functor.Precoverage.IsCocontinuous v K K' := h.isCocontinuous
  inferInstance

/-- The composite of an augmentation functor with a compatible presenting functor is
cocontinuous. -/
@[reducible] def IsCompatible.isCocontinuous_compFunctor :
    (u0 ⋙ v).IsCocontinuous (J (op ⦋0⦌)).toGrothendieck K'.toGrothendieck :=
  -- Local instance justification (search instability): topology-level IsCocontinuous of this presenting v comes from IsCompatible and cannot be a unique global instance.
  letI : v.IsCocontinuous K.toGrothendieck K'.toGrothendieck :=
    isCocontinuous_topology J J' K K' u0 u0' α v
  CategoryTheory.isCocontinuous_comp u0 v (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck

/-- The morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` induced by the cocontinuous functor `v`. -/
def IsCompatible.topos : MorphismOfTopoiIn K'.toGrothendieck K.toGrothendieck :=
  -- Local instance justification (search instability): morphismOfTopoiInOfCocontinuous needs IsCocontinuous of this presenting v from IsCompatible, not a unique global instance.
  letI : v.IsCocontinuous K.toGrothendieck K'.toGrothendieck :=
    isCocontinuous_topology J J' K K' u0 u0' α v
  v.morphismOfTopoiInOfCocontinuous K.toGrothendieck K'.toGrothendieck

/-- Inverse image of `IsCompatible.topos` is cocontinuous sheaf pullback along `v`. -/
theorem IsCompatible.topos_inverseImage :
    (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage =
      v.sheafPullbackCocontinuous (Type w) K.toGrothendieck K'.toGrothendieck :=
  sorry

/-- Inverse images of `a'₀ ∘ h₀` and `h₋₁ ∘ a₀` are canonically isomorphic as morphisms of
topoi, by composition of cocontinuous functors in Sites Lemma 7.21.2. -/
def IsCompatible.inverseImage_comp :
    (IsAugmentation.toposMap F' J' K' u0').inverseImage ⋙
        (IsFiberwiseMorphism.topos J J' α ⦋0⦌).inverseImage ≅
      (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage ⋙
        (IsAugmentation.toposMap F J K u0).inverseImage :=
  -- Local instance justification (search instability): sheafPullbackCocontinuousAdjunction needs IsCocontinuous of this presenting v from IsCompatible, not a unique global instance.
  letI : v.IsCocontinuous K.toGrothendieck K'.toGrothendieck :=
    isCocontinuous_topology J J' K K' u0 u0' α v
  -- Local instance justification (search instability): IsCocontinuous of u0 ⋙ v depends on IsCompatible data not recoverable from the composite functor alone.
  letI : (u0 ⋙ v).IsCocontinuous (J (op ⦋0⦌)).toGrothendieck K'.toGrothendieck :=
    isCocontinuous_compFunctor J J' K K' u0 u0' α v
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        (u0'.sheafPullbackCocontinuousAdjunction
          (J' (op ⦋0⦌)).toGrothendieck K'.toGrothendieck)
        ((α.app (op ⦋0⦌)).toFunctor.sheafPullbackCocontinuousAdjunction
          (J (op ⦋0⦌)).toGrothendieck (J' (op ⦋0⦌)).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousComp'
          (J (op ⦋0⦌)).toGrothendieck (J' (op ⦋0⦌)).toGrothendieck K'.toGrothendieck
          (α.app (op ⦋0⦌)).toFunctor u0' (eqToIso h.comp_eq) ≪≫
        (Functor.sheafPushforwardCocontinuousComp'
          (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck K'.toGrothendieck
          u0 v (Iso.refl _)).symm))
    (Adjunction.comp
      (v.sheafPullbackCocontinuousAdjunction K.toGrothendieck K'.toGrothendieck)
      (u0.sheafPullbackCocontinuousAdjunction
        (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck))

/-- The comparison `IsCompatible.inverseImage_comp` is invertible. -/
theorem IsCompatible.inverseImage_comp_hom_comp_inv :
    (IsCompatible.inverseImage_comp J J' K K' u0 u0' α v).hom ≫
      (IsCompatible.inverseImage_comp J J' K K' u0 u0' α v).inv = 𝟙 _ :=
  sorry

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
