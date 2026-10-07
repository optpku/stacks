module

public import stacks_project.Chap111.Definition_111_30_6_QuasiIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 111.30.6: for an abelian category `𝒜`, a morphism `α : K ⟶ L` of cochain complexes
of `Fil(𝒜)` (`FilteredComplex 𝒜`) is a filtered quasi-isomorphism when for each `p : ℤ` the
induced map `gr^p(K) ⟶ gr^p(L)` (`FilteredComplex.gradedPieceMap α p`) is a quasi-isomorphism. -/
@[stacks 028D] #check @FilteredComplex.IsFilteredQuasiIso
