/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.Duality
import StacksCheckRecall

@[expose] public section
open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped DerivedCategory.CohomologyIn
universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
variable (K : DerivedQCoh X)
variable (hK : IsDualizingComplex K)

/- Lemma 86.2.4 (1): a dualizing complex on a locally Noetherian algebraic space has coherent cohomology. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentCohomology K hK :
  DerivedCategory.cohomologyIn (SheafOfModules.isCoherent (structureSheaf X)) K.obj)

/- Lemma 86.2.4 (2): derived internal Hom into a dualizing complex is an anti-equivalence. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentDualityIsEquivalence K hK :
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentDuality K hK).IsEquivalence)

/- Lemma 86.2.4 (3): the canonical bidual transformation is an isomorphism. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentBidualIsIso K hK :
  IsIso (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.coherentBidual K hK))

section
variable [IsQuasiCompact X]

/- Lemma 86.2.4 (4): under quasi-compactness, duality exchanges bounded-below and bounded-above complexes. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.plusDualityIsEquivalence K hK :
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.plusDuality K hK).IsEquivalence)

/- Lemma 86.2.4 (5): under quasi-compactness, duality is an anti-equivalence on bounded coherent complexes. -/
@[stacks 0E51] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.boundedDualityIsEquivalence K hK :
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.boundedDuality K hK).IsEquivalence)

end

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
