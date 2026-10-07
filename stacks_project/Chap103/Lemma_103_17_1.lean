module

public import stacks_project.Chap103.Lemma_103_17_1_Coherent
public import stacks_project.Chap103.Lemma_103_17_1_Restrict
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
variable (F : SheafOfModules.{u} (structureSheaf X))

/- Lemma 103.17.1 (1): on a locally Noetherian algebraic stack `X`, an `𝒪_X`-module
`F` is of finite presentation iff it is quasi-coherent and of finite type. -/
@[stacks 0GR5]
#check (isFinitePresentation_iff_isQuasicoherent_and_isFiniteType F :
  F.IsFinitePresentation ↔ F.IsQuasicoherent ∧ F.IsFiniteType)

/- Lemma 103.17.1 (2): `F` is of finite presentation iff it is quasi-coherent and
for every morphism `f : U.toGroupoids ⟶ X` from a locally Noetherian algebraic
space, `f^* F |_{U_étale}` is coherent. -/
@[stacks 0GR5]
#check (isFinitePresentation_iff_forall_locallyNoetherian F :
  F.IsFinitePresentation ↔
    F.IsQuasicoherent ∧
      ∀ (U : AlgebraicSpace S) [AlgebraicSpace.IsLocallyNoetherian U]
        (f : U.toGroupoids ⟶ X),
        ((restrictPullback f).obj F).IsCoherent)

/- Lemma 103.17.1 (3): `F` is of finite presentation iff it is quasi-coherent and
there exists an algebraic space `U` and a locally of finite type, flat, surjective
morphism `f : U.toGroupoids ⟶ X` such that `f^* F |_{U_étale}` is coherent. -/
@[stacks 0GR5]
#check (isFinitePresentation_iff_exists_locallyOfFiniteType_flat_surjective F :
  F.IsFinitePresentation ↔
    F.IsQuasicoherent ∧
      ∃ (U : AlgebraicSpace S) (f : U.toGroupoids ⟶ X),
        LocallyOfFiniteType f ∧ Flat f ∧ Surjective f ∧
          ((restrictPullback f).obj F).IsCoherent)

end AlgebraicGeometry.AlgebraicStack
