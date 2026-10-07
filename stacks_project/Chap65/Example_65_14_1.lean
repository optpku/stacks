module

public import stacks_project.Chap65.Example_65_14_1_Relation
public import stacks_project.Chap65.Example_65_14_1_Space
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- Example 65.14.1 (1): the projections `s, t : R ⟶ U` are étale, and hence `j` is an étale
equivalence relation. -/
@[stacks 02Z1]
#check
  (instIsEtaleEquivalenceRelation_preRelation :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)], (preRelation k).IsEtaleEquivalenceRelation)

/- Example 65.14.1 (2): the quotient `X = U / R` is an algebraic space by Theorem 65.10.5. -/
@[stacks 02Z1]
#check sheafOfPoints_spec

/- Example 65.14.1 (3): the relation scheme `R = Δ ⨿ Γ` is quasi-compact. -/
@[stacks 02Z1]
#check
  (instCompactSpace_relationOver :
    ∀ (k : Type u) [Field k], CompactSpace (relationOver k).left)

/- Example 65.14.1 (4): since `R` is quasi-compact, `X` is quasi-separated. -/
@[stacks 02Z1]
#check quasiCompact_diag_sheafOfPoints

/- Example 65.14.1 (5): the morphism `j : R ⟶ U ×_k U` is not an immersion. -/
@[stacks 02Z1]
#check not_isImmersion_relationHom

/- Example 65.14.1 (6): `X` is not locally separated because `j` is not an immersion. -/
@[stacks 02Z1]
#check not_isImmersion_diag_sheafOfPoints
