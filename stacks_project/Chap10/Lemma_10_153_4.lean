/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Finite
public import ReasLib.RingTheory.Henselian.QuasiFinite
public import ReasLib.RingTheory.LocalRing.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.153.4

@stack 04GH

Lemma 10.153.4 is recalled through the neutral finite-product and primewise
quasi-finite localization owners.  The source-specific `PrimeSpectrum`
packaging is not a new mathematical owner: the reusable API works directly
with a prime ideal and its canonical localization.
-/

/- Lemma 10.153.4, tag `04GH`: finite algebras over henselian local rings
split into finite henselian-local factors, and quasi-finite points above the
closed point become henselian and module-finite after localization. -/
@[stacks 04GH "(1) finite product decomposition data"]
#check @HenselianLocalRing.FiniteProduct

@[stacks 04GH "(1) finite product decomposition"]
#check @HenselianLocalRing.FiniteProduct.nonempty

@[stacks 04GH "(2) local factor of a finite product"]
#check @HenselianLocalRing.FiniteProduct.henselian

@[stacks 04GH "(2) finite local ring map has henselian target"]
#check @HenselianLocalRing.of_finite

@[stacks 04GH "(2) finite map between local rings is local"]
#check @RingHom.isLocalHom_of_finite

@[stacks 04GH "(2) canonical finite local algebra is henselian"]
#check @HenselianLocalRing.of_moduleFinite

@[stacks 04GH "(2) canonical finite local algebra map"]
#check @Algebra.isLocalHom_of_moduleFinite

@[stacks 04GH "(3) henselian localization at a quasi-finite point"]
#check @HenselianLocalRing.QuasiFiniteAt.localizationAtPrime_henselian

@[stacks 04GH "(3) finite localization at a quasi-finite point"]
#check @HenselianLocalRing.QuasiFiniteAt.localizationAtPrime_moduleFinite

@[stacks 04GH "(4) henselian localization of a quasi-finite algebra"]
#check @HenselianLocalRing.QuasiFinite.localizationAtPrime_henselian

@[stacks 04GH "(4) finite localization of a quasi-finite algebra"]
#check @HenselianLocalRing.QuasiFinite.localizationAtPrime_moduleFinite
