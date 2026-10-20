module

public import stacks_project.Chap85.Remark_85_4_1_Fiberwise
public import stacks_project.Chap85.Remark_85_4_1_MorphismDiagram
import StacksCheckRecall

/-!
# Remark 85.4.1

In Situation 85.3.3, an augmentation `a0` towards a site `D` is either a
morphism of sites `C.obj ⦋0⦌ ⟶ D` presented by a continuous functor `u0`, or a
morphism of topoi `Sh(C0) ⟶ Sh(D)` presented by a cocontinuous functor `u0`,
with composites along all `φ : ⦋0⦌ ⟶ n` independent of `φ`.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial

/- Remark 85.4.1 (1): case A, a morphism of sites `a0 : C.obj ⦋0⦌ ⟶ D` given by
a continuous functor `u0 : D ⥤ C.obj ⦋0⦌` such that `u_φ ∘ u0` is independent of
`φ : ⦋0⦌ ⟶ n`. -/
@[stacks 0D6Z] #check (CategoryTheory.SimplicialSites.IsAugmentation.iff :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    {D : Type u} [Category.{v} D] (K : Precoverage D) (u0 : D ⥤ C.obj ⦋0⦌)
    [HasWeakSheafify (J ⦋0⦌).toGrothendieck (Type w)]
    [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P],
    CategoryTheory.SimplicialSites.IsAugmentation C J K u0 ↔
      IsExactMorphismOfSites K.toGrothendieck (J ⦋0⦌).toGrothendieck u0 ∧
        ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
          u0 ⋙ (C.map φ).toFunctor = u0 ⋙ (C.map ψ).toFunctor)

/- Remark 85.4.1 (2): case B, a morphism of topoi `a0 : Sh(C0) ⟶ Sh(D)` given by
a cocontinuous functor `u0 : C0 ⥤ D` such that `u0 ∘ u_φ` is independent of
`φ : ⦋0⦌ ⟶ n`. -/
@[stacks 0D6Z] #check (CategoryTheory.Grothendieck.IsAugmentation.iff :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
    {D : Type u} [Category.{v} D] (K : Precoverage D) (u0 : F.obj (op ⦋0⦌) ⥤ D),
    CategoryTheory.Grothendieck.IsAugmentation F J K u0 ↔
      Functor.Precoverage.IsCocontinuous u0 (J (op ⦋0⦌)) K ∧
        ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
          (F.map φ.op).toFunctor ⋙ u0 = (F.map ψ.op).toFunctor ⋙ u0)
