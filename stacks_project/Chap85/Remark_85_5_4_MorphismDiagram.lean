/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Remark_85_4_1_MorphismDiagram
public import stacks_project.Chap85.Remark_85_5_1_Morphism

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
  -- Local instance justification (search instability): IsContinuous of this presenting v is a parent of IsCompatible.isExact, whose extra J/α/u0 parameters cannot be synthesized from v.
  letI : v.IsContinuous K'.toGrothendieck K.toGrothendieck := h.isExact.toIsContinuous
  -- Local instance justification (search instability): PreservesFiniteLimits of v.sheafPullback is a field of IsCompatible.isExact and cannot be a unique global instance on v.
  letI : PreservesFiniteLimits
      (v.sheafPullback (Type w) K'.toGrothendieck K.toGrothendieck) :=
    h.isExact.preservesFiniteLimits_sheafPullback
  v.morphismOfTopoiInOfContinuous K'.toGrothendieck K.toGrothendieck

/-- Inverse image of `IsCompatible.topos` is sheaf pullback along `v`. -/
theorem IsCompatible.topos_inverseImage :
    (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage =
      @Functor.sheafPullback _ _ _ _ v (Type w) _ K'.toGrothendieck K.toGrothendieck
        h.isExact.toIsContinuous _ :=
  sorry

/-- Inverse images of `a'₀ ∘ h₀` and `h₋₁ ∘ a₀` are canonically isomorphic as morphisms of
topoi, by the continuous-square comparison for Sites Definition 7.14.5. -/
def IsCompatible.inverseImage_comp :
    (IsAugmentation.toposMap C' J' K' u0').inverseImage ⋙
        (IsMorphism.topos J J' α ⦋0⦌).inverseImage ≅
      (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage ⋙
        (IsAugmentation.toposMap C J K u0).inverseImage :=
  -- Local instance justification (search instability): ContinuousSquare.pullbackIso needs IsContinuous of this presenting v from IsCompatible, not a unique global instance.
  letI : v.IsContinuous K'.toGrothendieck K.toGrothendieck := h.isExact.toIsContinuous
  Functor.ContinuousSquare.pullbackIso (Type w) h.comp_eq.symm

/-- The continuous-square comparison `IsCompatible.inverseImage_comp` is invertible. -/
theorem IsCompatible.inverseImage_comp_hom_comp_inv :
    (IsCompatible.inverseImage_comp J J' K K' u0 u0' α v).hom ≫
      (IsCompatible.inverseImage_comp J J' K K' u0 u0' α v).inv = 𝟙 _ :=
  sorry

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
