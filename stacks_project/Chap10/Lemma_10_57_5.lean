/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.ProjectiveSpectrum
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.57.5

The ring and module localizations on a projective-spectrum basic open are
recalled from their canonical owners.  The selected scalar actions are named
support data in `ReasLib`, rather than chapter-local instances.

@stack 00JR
-/

-- Lemma 10.57.5 (1): the ring at a point of a basic open is the corresponding localization.
@[stacks 00JR "(1), ring localization"]
#check @AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime

-- Lemma 10.57.5 (2): the module comparison is the corresponding module localization.
@[stacks 00JR "(2), module localization"]
#check @HomogeneousLocalization.Module.awayToAtPrime_isLocalizedModule

@[stacks 00JR "module comparison map"]
#check @HomogeneousLocalization.Module.awayToAtPrime

@[stacks 00JR "module comparison on fractions"]
#check @HomogeneousLocalization.Module.awayToAtPrime_apply

@[stacks 00JR "selected scalar support"]
#check @HomogeneousLocalization.Module.awayAtPrimeAlgebra
#check @HomogeneousLocalization.Module.awayAtPrimeModule
#check @HomogeneousLocalization.Module.awayAtPrimeTower
