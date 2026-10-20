module

public import stacks_project.Chap85.Remark_85_5_4_Fiberwise
public import stacks_project.Chap85.Remark_85_5_4_MorphismDiagram
import StacksCheckRecall

/-!
# Remark 85.5.4

In Situation 85.3.3, with augmentations `a0`, `a'0` as in Remark 85.4.1 and a
morphism `h` of simplicial sites as in Remark 85.5.1, a morphism of topoi
`h₋₁ : Sh(D) ⟶ Sh(D')` is compatible with `h`, `a0`, `a'0` when it is presented
by a morphism of sites (case A) or a cocontinuous functor (case B) closing the
degree-zero square. In both cases the same square commutes as morphisms of
topoi.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

section

open CategoryTheory.SimplicialSites

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


/- Remark 85.5.4 (1)
In Situation 85.3.3 case A, a morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` is
compatible with `h`, `a0`, `a'0` if it comes from a morphism of sites
`h₋₁ : D ⟶ D'` presented by `v : D' ⥤ D` such that
`u0' ⋙ (α.app ⦋0⦌).toFunctor = v ⋙ u0` as morphisms of sites. The same square
commutes as morphisms of topoi, see Sites Definition 7.14.5. -/
@[stacks 0D98] #check (CategoryTheory.SimplicialSites.IsCompatible.iff J J' K K' u0 u0' α v :
  CategoryTheory.SimplicialSites.IsCompatible J J' K K' u0 u0' α v ↔
    IsExactMorphismOfSites K'.toGrothendieck K.toGrothendieck v ∧
      u0' ⋙ (α.app ⦋0⦌).toFunctor = v ⋙ u0)

variable [h : CategoryTheory.SimplicialSites.IsCompatible J J' K K' u0 u0' α v]

#check (CategoryTheory.SimplicialSites.IsCompatible.topos J J' K K' u0 u0' α v :
  MorphismOfTopoiIn K'.toGrothendieck K.toGrothendieck)

#check (CategoryTheory.SimplicialSites.IsCompatible.inverseImage_comp J J' K K' u0 u0' α v :
  u0'.sheafPullback (Type w) K'.toGrothendieck (J' ⦋0⦌).toGrothendieck ⋙
      (CategoryTheory.SimplicialSites.IsMorphism.topos J J' α ⦋0⦌).inverseImage ≅
    (CategoryTheory.SimplicialSites.IsCompatible.topos J J' K K' u0 u0' α v).inverseImage ⋙
      u0.sheafPullback (Type w) K.toGrothendieck (J ⦋0⦌).toGrothendieck)

end

section

open CategoryTheory.Grothendieck

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


/- Remark 85.5.4 (2)
In Situation 85.3.3 case B, a morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` is
compatible with `h`, `a0`, `a'0` if it comes from a cocontinuous functor
`v : D ⥤ D'` such that `(α.app (op ⦋0⦌)).toFunctor ⋙ u0' = u0 ⋙ v` as functors.
The same square commutes as morphisms of topoi, see Sites Lemma 7.21.2. -/
@[stacks 0D98] #check (CategoryTheory.Grothendieck.IsCompatible.iff J J' K K' u0 u0' α v :
  CategoryTheory.Grothendieck.IsCompatible J J' K K' u0 u0' α v ↔
    Functor.Precoverage.IsCocontinuous v K K' ∧
      (α.app (op ⦋0⦌)).toFunctor ⋙ u0' = u0 ⋙ v)

variable [h : CategoryTheory.Grothendieck.IsCompatible J J' K K' u0 u0' α v]

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

#check (CategoryTheory.Grothendieck.IsCompatible.topos J J' K K' u0 u0' α v :
  MorphismOfTopoiIn K'.toGrothendieck K.toGrothendieck)

#check (CategoryTheory.Grothendieck.IsCompatible.inverseImage_comp J J' K K' u0 u0' α v :
  u0'.sheafPullbackCocontinuous (Type w) (J' (op ⦋0⦌)).toGrothendieck K'.toGrothendieck ⋙
      (CategoryTheory.Grothendieck.IsFiberwiseMorphism.topos J J' α ⦋0⦌).inverseImage ≅
    (CategoryTheory.Grothendieck.IsCompatible.topos J J' K K' u0 u0' α v).inverseImage ⋙
      u0.sheafPullbackCocontinuous (Type w) (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck)

end
