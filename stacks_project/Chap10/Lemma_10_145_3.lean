/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Neighborhood.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Quasi-finite decomposition after an etale neighborhood

@stack 00UK

The reusable owner bundles the etale neighborhood, product factors, selected fiber points,
and residual factor.  This preserves the concrete data of the source existence statement while
preventing downstream users from rebuilding its dependent instances.
-/

/- Lemma 10.145.3: a finite-type algebra admits a finite-product decomposition after an etale
neighborhood of a selected prime, with finite one-point factors and a remainder having no
quasi-finite point over the selected neighborhood point. -/
@[stacks 00UK "existence"]
#check @PrimeSpectrum.EtaleNeighborhood.QuasiFiniteDecomposition.nonempty

@[stacks 00UK "explicit decomposition constructor"]
#check @PrimeSpectrum.EtaleNeighborhood.QuasiFiniteDecomposition.of

/- The specification exposes the etale, residue-field, finiteness, unique-prime, and remainder
properties carried by the decomposition. -/
@[stacks 00UK "specification"]
#check @PrimeSpectrum.EtaleNeighborhood.QuasiFiniteDecomposition.spec
