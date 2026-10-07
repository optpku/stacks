module

public import stacks_project.Chap72.Lemma_72_4_2_Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 72.4.2: Let `S` be a scheme. Let `X` be an integral algebraic space over `S`.
Let `η` be the generic point of `|X|`. There are canonical identifications
`R(X) = O_{X,η}^h = κ(η)`, realized as ring equivalences
`RationalFunction X ≃+* henselianLocalRing X η ≃+* ULift (X.residueField η)`
for `η ∈ genericPoints X`, where `RationalFunction X` is the ring of rational
functions, `X.residueField η` is the residue field, and `henselianLocalRing X η`
is the henselian local ring at `η`. In particular, these rings are fields. -/
@[stacks 0END] #check rationalFunctionRingEquivHenselianLocalRing
@[stacks 0END] #check henselianLocalRingEquivResidueField
@[stacks 0END] #check rationalFunctionRingEquivResidueField
@[stacks 0END] #check instField_rationalFunctionRing
@[stacks 0END] #check field_henselianLocalRing_genericPoint
