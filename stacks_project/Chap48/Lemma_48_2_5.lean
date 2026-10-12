/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Duality
import StacksCheckRecall

@[expose] public section
open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped DerivedCategory.CohomologyIn
universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
variable (K : RingedSpace.ModuleDerived X.toRingedSpace)
variable (hK : IsDualizingComplex K)

/- Lemma 48.2.5 (1): a dualizing complex on a locally Noetherian scheme has coherent cohomology. -/
@[stacks 0A89] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.coherentCohomology K hK :
  DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K)

/- Lemma 48.2.5 (2): derived internal Hom into a dualizing complex is an anti-equivalence. -/
@[stacks 0A89] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.coherentDualityIsEquivalence H K hK :
  (AlgebraicGeometry.Scheme.IsDualizingComplex.coherentDuality H K hK).IsEquivalence)

/- Lemma 48.2.5 (3): the canonical bidual transformation is an isomorphism. -/
@[stacks 0A89] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.coherentBidualIsIso H K hK :
  IsIso (AlgebraicGeometry.Scheme.IsDualizingComplex.coherentBidual H K hK))

section
variable [CompactSpace X]

/- Lemma 48.2.5 (4): under quasi-compactness, duality exchanges bounded-below and bounded-above complexes. -/
@[stacks 0A89] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.plusDualityIsEquivalence H K hK :
  (AlgebraicGeometry.Scheme.IsDualizingComplex.plusDuality H K hK).IsEquivalence)

/- Lemma 48.2.5 (5): under quasi-compactness, duality is an anti-equivalence on bounded coherent complexes. -/
@[stacks 0A89] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.boundedDualityIsEquivalence H K hK :
  (AlgebraicGeometry.Scheme.IsDualizingComplex.boundedDuality H K hK).IsEquivalence)

end

end AlgebraicGeometry.Scheme.IsDualizingComplex
