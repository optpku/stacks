/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos

/-!
# Morphisms of fiberwise simplicial sites

A natural transformation with cocontinuous component functors induces
stagewise morphisms of topoi. Its naturality squares induce canonical
comparisons between their composites with the simplex structure maps.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
include instF instF'

/-- A morphism of fiberwise simplicial sites: a natural
transformation `α : F ⟶ F'` whose component functors
`(α.app n).toFunctor : F.obj n ⥤ F'.obj n` are cocontinuous. Each component induces a
morphism of topoi `h_n : Sh(F.obj n) ⟶ Sh(F'.obj n)`. Property `P` is not required of
these components. -/
class IsFiberwiseMorphism (α : F ⟶ F') : Prop where
  /-- Each component functor is cocontinuous for the fiber topologies. -/
  isCocontinuous : ∀ n, ((α.app n).toFunctor).IsCocontinuous
    (J n).toGrothendieck (J' n).toGrothendieck

/-- A natural transformation of fiberwise simplicial sites is a morphism of simplicial sites
iff every component functor is cocontinuous. -/
theorem IsFiberwiseMorphism.iff (α : F ⟶ F') :
    IsFiberwiseMorphism J J' α ↔
      ∀ n, ((α.app n).toFunctor).IsCocontinuous (J n).toGrothendieck (J' n).toGrothendieck :=
  sorry

/-- The identity transformation of a fiberwise simplicial site is a morphism of simplicial
sites. -/
instance IsFiberwiseMorphism.id : IsFiberwiseMorphism J J (𝟙 F) :=
  sorry

variable (α : F ⟶ F')
variable [hα : IsFiberwiseMorphism J J' α]
include hα

/-- Every component of a fiberwise morphism of simplicial sites is cocontinuous. -/
instance IsFiberwiseMorphism.instIsCocontinuous (n : SimplexCategoryᵒᵖ) :
    ((α.app n).toFunctor).IsCocontinuous (J n).toGrothendieck (J' n).toGrothendieck :=
  hα.isCocontinuous n

/-- Naturality of `α` as functors of stage categories: `u_φ ⋙ v_m = v_n ⋙ u'_φ`. -/
theorem IsFiberwiseMorphism.naturality_toFunctor {m n : SimplexCategory} (φ : m ⟶ n) :
    (F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor =
      (α.app (op n)).toFunctor ⋙ (F'.map φ.op).toFunctor :=
  sorry

variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The morphism of topoi `h_n : Sh(F.obj (op n)) ⟶ Sh(F'.obj (op n))` induced by the
cocontinuous component `(α.app (op n)).toFunctor : F.obj (op n) ⥤ F'.obj (op n)`. -/
def IsFiberwiseMorphism.topos (n : SimplexCategory) :
    MorphismOfTopoiIn (J' (op n)).toGrothendieck (J (op n)).toGrothendieck :=
  (α.app (op n)).toFunctor.morphismOfTopoiInOfCocontinuous
    (J (op n)).toGrothendieck (J' (op n)).toGrothendieck

/-- Inverse image of `IsFiberwiseMorphism.topos` is cocontinuous sheaf pullback along the
component functor. -/
theorem IsFiberwiseMorphism.topos_inverseImage (n : SimplexCategory) :
    (IsFiberwiseMorphism.topos J J' α n).inverseImage =
      (α.app (op n)).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (J' (op n)).toGrothendieck :=
  sorry

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Structure maps of the source followed by a fiberwise morphism component are cocontinuous. -/
instance IsFiberwiseMorphism.instIsCocontinuous_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    ((F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor).IsCocontinuous
      (J (op n)).toGrothendieck (J' (op m)).toGrothendieck :=
  isCocontinuous_comp (F.map φ.op).toFunctor (α.app (op m)).toFunctor
    (J (op n)).toGrothendieck (J (op m)).toGrothendieck

/-- Inverse images of `f'_φ ∘ h_n` and `h_m ∘ f_φ` are canonically isomorphic, as morphisms of
topoi, by composition of cocontinuous functors. -/
def IsFiberwiseMorphism.inverseImage_naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    (toposMap F' J' φ).inverseImage ⋙ (IsFiberwiseMorphism.topos J J' α n).inverseImage ≅
      (IsFiberwiseMorphism.topos J J' α m).inverseImage ⋙ (toposMap F J φ).inverseImage :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((F'.map φ.op).toFunctor.sheafPullbackCocontinuousAdjunction
          (J' (op n)).toGrothendieck (J' (op m)).toGrothendieck)
        ((α.app (op n)).toFunctor.sheafPullbackCocontinuousAdjunction
          (J (op n)).toGrothendieck (J' (op n)).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousComp'
          (J (op n)).toGrothendieck (J' (op n)).toGrothendieck (J' (op m)).toGrothendieck
          (α.app (op n)).toFunctor (F'.map φ.op).toFunctor
          (eqToIso
            (((Cat.Hom.comp_toFunctor (α.app (op n)) (F'.map φ.op)).symm).trans
              ((congrArg Cat.Hom.toFunctor (α.naturality φ.op).symm).trans
                (Cat.Hom.comp_toFunctor (F.map φ.op) (α.app (op m)))))) ≪≫
        (Functor.sheafPushforwardCocontinuousComp'
          (J (op n)).toGrothendieck (J (op m)).toGrothendieck (J' (op m)).toGrothendieck
          (F.map φ.op).toFunctor (α.app (op m)).toFunctor (Iso.refl _)).symm))
    (Adjunction.comp
      ((α.app (op m)).toFunctor.sheafPullbackCocontinuousAdjunction
        (J (op m)).toGrothendieck (J' (op m)).toGrothendieck)
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuousAdjunction
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck))

end CategoryTheory.Grothendieck

