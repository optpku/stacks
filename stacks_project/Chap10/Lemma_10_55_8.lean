module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.55.8

The local freeness of finite projective modules and the resulting rank identification of
`K₀(R)` with `ℤ` are recalled from their ReasLib owners.

@stack 00JJ
-/

/- Lemma 10.55.8 (1): every finite projective module over a local ring is
finite free. -/
@[stacks 00JJ "finite projective modules over local rings are free"]
#check @Module.FiniteProjective.free_of_isLocalRing

/- Lemma 10.55.8 (2): module rank descends to an additive map
`K₀(R) →+ ℤ`. -/
@[stacks 00JJ "rank homomorphism"]
#check @CategoryTheory.ModuleCat.K0.Projective.rank

/- Lemma 10.55.8 (3): rank identifies `K₀(R)` with `ℤ`. -/
@[stacks 00JJ "rank equivalence"]
#check @CategoryTheory.ModuleCat.K0.Projective.rankEquiv
