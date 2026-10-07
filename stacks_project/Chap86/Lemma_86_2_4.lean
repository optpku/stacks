module

public import stacks_project.Chap86.Lemma_86_2_4_Duality
import StacksCheckRecall

@[expose] public section
open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped DerivedCategory.CohomologyIn
universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable (H : MonoidalClosed (ModuleDerived X))
variable (K : DerivedQCoh X)
variable (hK : IsDualizingComplex K)

/- Lemma 86.2.4 (1): a dualizing complex on a locally Noetherian algebraic space has coherent cohomology. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentCohomology K hK :
  DerivedCategory.cohomologyIn (SheafOfModules.isCoherent (structureSheaf X)) K.obj)

/- Lemma 86.2.4 (2): derived internal Hom into a dualizing complex is an anti-equivalence. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentDualityIsEquivalence H K hK :
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentDuality H K hK).IsEquivalence)

/- Lemma 86.2.4 (3): the canonical bidual transformation is an isomorphism. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentBidualIsIso H K hK :
  IsIso (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentBidual H K hK))

section
variable [IsQuasiCompact X]

/- Lemma 86.2.4 (4): under quasi-compactness, duality exchanges bounded-below and bounded-above complexes. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.plusDualityIsEquivalence H K hK :
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.plusDuality H K hK).IsEquivalence)

/- Lemma 86.2.4 (5): under quasi-compactness, duality is an anti-equivalence on bounded coherent complexes. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.boundedDualityIsEquivalence H K hK :
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.boundedDuality H K hK).IsEquivalence)

end

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
