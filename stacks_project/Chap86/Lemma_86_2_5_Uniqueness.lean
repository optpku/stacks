module

public import stacks_project.Chap86.Definition_86_2_2_DualizingComplex
public import stacks_project.Chap75.Lemma_75_5_6_Instances

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.DerivedCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex

/-- Any two dualizing complexes on a locally Noetherian algebraic space differ, up to
isomorphism in `D(𝒪_X)`, by derived tensor with an object `L` of `D(𝒪_X)` for which
fixed-right derived tensor `- ⊗^L L` is an equivalence. -/
theorem existsInvertibleTensorIso
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K K' : DerivedQCoh X} (hK : IsDualizingComplex K)
    (hK' : IsDualizingComplex K') :
    ∃ L : ModuleDerived X,
      (DerivedTensor.Right.functor L).IsEquivalence ∧
        Nonempty (K'.obj ≅ DerivedTensor.Right.obj K.obj L) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
