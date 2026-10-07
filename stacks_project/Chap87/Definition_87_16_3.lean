module

public import stacks_project.Chap87.Definition_87_16_3_Separation
import StacksCheckRecall

@[expose] public section

/- Definition 87.16.3 (1): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. We say `X` is quasi-separated if the equivalent conditions of
Lemma 87.16.1 are satisfied. -/
@[stacks 0AJ7] #check AlgebraicGeometry.IsFormalAlgebraicSpace.IsQuasiSeparated

/- Definition 87.16.3 (2): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. We say `X` is separated if the equivalent conditions of
Lemma 87.16.2 are satisfied. -/
@[stacks 0AJ7] #check AlgebraicGeometry.IsFormalAlgebraicSpace.IsSeparated
