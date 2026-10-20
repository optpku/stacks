module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 43.13.3 (1): the diagonal of a nonsingular variety is a regular immersion. -/
@[stacks 0B0Q] #check
  (AlgebraicGeometry.SchemeOverField.diagonal_isRegularImmersion :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Variety X]
      [Scheme.Regular X.left], IsRegularImmersion (pullback.diagonal X.hom))

/- Lemma 43.13.3 (2): the conormal sheaf of the diagonal of a nonsingular variety has
rank equal to the dimension of the variety. -/
@[stacks 0B0Q] #check
  (AlgebraicGeometry.SchemeOverField.diagonal_conormal_isFiniteLocallyFreeOfRank :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Variety X]
      [Scheme.Regular X.left],
      Scheme.Modules.IsFiniteLocallyFreeOfRank
        (baseFieldTrdegAt X (genericPoint X.left))
        (Scheme.Hom.conormalSheaf (pullback.diagonal X.hom)))

end AlgebraicGeometry.SchemeOverField
