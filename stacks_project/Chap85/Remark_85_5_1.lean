/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Morphism
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialMorphism
import StacksCheckRecall

/-!
# Remark 85.5.1

A morphism of simplicial sites in Situation 85.3.3 is either a stagewise family
of morphisms of sites (case A) or a stagewise family of cocontinuous functors
(case B). In both cases the same square commutes as morphisms of topoi.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

section

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [SimplicialSites.IsMorphismDiagram C J] [SimplicialSites.IsMorphismDiagram C' J']
variable (α : C' ⟶ C)
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [SimplicialSites.IsMorphism J J' α]
variable {m n : SimplexCategory} (φ : m ⟶ n)

/- Remark 85.5.1 (1)
In Situation 85.3.3 case A, a morphism of simplicial sites is a family of
morphisms of sites `h_n : C.obj n ⟶ C'.obj n` presented by functors
`(α.app n).toFunctor : C'.obj n ⥤ C.obj n`, with
`f'_φ ∘ h_n = h_m ∘ f_φ` as morphisms of sites for all `φ : m ⟶ n`.
The same square commutes as morphisms of topoi, see Sites Definition 7.14.5. -/
@[stacks 0D95] #check
  (CategoryTheory.SimplicialSites.IsMorphism J J' : (C' ⟶ C) → Prop)
#check (CategoryTheory.SimplicialSites.IsMorphism.naturality_toFunctor J J' α φ :
  (C'.map φ).toFunctor ⋙ (α.app n).toFunctor =
    (α.app m).toFunctor ⋙ (C.map φ).toFunctor)
#check (CategoryTheory.SimplicialSites.IsMorphism.topos J J' α n :
  MorphismOfTopoiIn (J' n).toGrothendieck (J n).toGrothendieck)
#check (CategoryTheory.SimplicialSites.IsMorphism.inverseImage_naturality J J' α φ :
  (CategoryTheory.SimplicialSites.toposMap C' J' φ).inverseImage ⋙
      (CategoryTheory.SimplicialSites.IsMorphism.topos J J' α n).inverseImage ≅
    (CategoryTheory.SimplicialSites.IsMorphism.topos J J' α m).inverseImage ⋙
      (CategoryTheory.SimplicialSites.toposMap C J φ).inverseImage)

end

section

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [Grothendieck.IsFiberwiseSite F J] [Grothendieck.IsFiberwiseSite F' J']
variable (α : F ⟶ F')
variable [Grothendieck.IsFiberwiseMorphism J J' α]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor).op.HasPointwiseRightKanExtension P]
variable {m n : SimplexCategory} (φ : m ⟶ n)

/- Remark 85.5.1 (2)
In Situation 85.3.3 case B, a morphism of simplicial sites is a family of
cocontinuous functors `v_n : C_n ⥤ C'_n` inducing morphisms of topoi
`h_n : Sh(C_n) ⟶ Sh(C'_n)`, with `u'_φ ∘ v_n = v_m ∘ u_φ` as functors for all
`φ : m ⟶ n`. The same square commutes as morphisms of topoi, see Sites
Lemma 7.21.2. -/
@[stacks 0D95] #check
  (CategoryTheory.Grothendieck.IsFiberwiseMorphism J J' : (F ⟶ F') → Prop)
#check (CategoryTheory.Grothendieck.IsFiberwiseMorphism.naturality_toFunctor J J' α φ :
  (F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor =
    (α.app (op n)).toFunctor ⋙ (F'.map φ.op).toFunctor)
#check (CategoryTheory.Grothendieck.IsFiberwiseMorphism.topos J J' α n :
  MorphismOfTopoiIn (J' (op n)).toGrothendieck (J (op n)).toGrothendieck)
#check (CategoryTheory.Grothendieck.IsFiberwiseMorphism.inverseImage_naturality J J' α φ :
  (CategoryTheory.Grothendieck.toposMap F' J' φ).inverseImage ⋙
      (CategoryTheory.Grothendieck.IsFiberwiseMorphism.topos J J' α n).inverseImage ≅
    (CategoryTheory.Grothendieck.IsFiberwiseMorphism.topos J J' α m).inverseImage ⋙
      (CategoryTheory.Grothendieck.toposMap F J φ).inverseImage)

end
