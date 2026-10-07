module

public import stacks_project.Chap75.Lemma_75_21_1_Criteria
public import stacks_project.Chap75.Lemma_75_21_3_InternalHom
public import stacks_project.Chap75.Lemma_75_21_3_Pullback
public import stacks_project.Chap75.Lemma_75_21_3_Tensor

/-!
# Inheritance of cohomology base change under derived tensor and internal Hom

On a cartesian square of algebraic spaces, the equivalent conditions of Lemma 75.21.1
pass from `L(g')^* K ⟶ K'` to the induced maps after `- ⊗^L K` and after `RHom(E, -)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.21.3 (1): on a cartesian square of algebraic spaces over a scheme `S`, if
`K` is in `D_QCoh(𝒪_X)` and `L(g')^* K ⟶ K'` satisfies the equivalent conditions of
Lemma 75.21.1, then for `E` in `D_QCoh(𝒪_X)` those conditions hold for
`L(g')^*(E ⊗^L K) ⟶ L(g')^* E ⊗^L K'`. -/
@[stacks 0DKI]
theorem cohomologyBaseChange_tensor {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (E : DerivedQCoh X) (hα : cohomologyBaseChangeHolds sq K K' α) :
    cohomologyBaseChangeHolds sq (tensorObj E K) (tensorObj (pullbackObj g' E) K')
      (tensorBaseChangeMap g' T_X T_X' E K K' α) :=
  sorry

/-- Lemma 75.21.3 (2): on a cartesian square of algebraic spaces over a scheme `S`, if
`K` is in `D_QCoh(𝒪_X)` and `L(g')^* K ⟶ K'` satisfies the equivalent conditions of
Lemma 75.21.1, then for `E` perfect in `D(𝒪_X)` those conditions hold for
`L(g')^* RHom(E, K) ⟶ RHom(L(g')^* E, K')`. -/
@[stacks 0DKI]
theorem cohomologyBaseChange_internalHom_of_isPerfect {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal] (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E)
    (hα : cohomologyBaseChangeHolds sq K K' α) :
    cohomologyBaseChangeHolds sq
      (internalHomObj H_X E K (derivedQCoh_of_perfect H_X E K hE))
      (internalHomObj H_X' ((ModuleDerived.pullback g').obj E) K'
        (internalHomTarget_mem_of_isPerfect g' H_X' E K' hE))
      (internalHomBaseChangeMap g' H_X H_X' E K K' α
        (derivedQCoh_of_perfect H_X E K hE)
        (internalHomTarget_mem_of_isPerfect g' H_X' E K' hE)) :=
  sorry

/-- Lemma 75.21.3 (3): on a cartesian square of algebraic spaces over a scheme `S`, if
`K` is bounded below in `D_QCoh(𝒪_X)` and `L(g')^* K ⟶ K'` satisfies the equivalent
conditions of Lemma 75.21.1, then for `E` pseudo-coherent in `D(𝒪_X)` those conditions
hold for `L(g')^* RHom(E, K) ⟶ RHom(L(g')^* E, K')`. -/
@[stacks 0DKI]
theorem cohomologyBaseChange_internalHom_of_isPseudoCoherent_of_boundedBelow
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal] (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (E : ModuleDerived X)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj)
    (hE : IsPseudoCoherent X E) (hα : cohomologyBaseChangeHolds sq K K' α) :
    cohomologyBaseChangeHolds sq
      (internalHomObj H_X E K (derivedQCoh_of_pseudoCoherent H_X E K hE hK))
      (internalHomObj H_X' ((ModuleDerived.pullback g').obj E) K'
        (internalHomTarget_mem_of_pseudoCoherent g' f' f g sq H_X' E K K' α hα hK hE))
      (internalHomBaseChangeMap g' H_X H_X' E K K' α
        (derivedQCoh_of_pseudoCoherent H_X E K hE hK)
        (internalHomTarget_mem_of_pseudoCoherent g' f' f g sq H_X' E K K' α hα hK hE)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
