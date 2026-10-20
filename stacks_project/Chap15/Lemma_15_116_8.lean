/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Kummer
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.8

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.117.8,
tag `09EX`.

The reusable owner is the canonical `DVR.Kummer.RootExtension`.  Its concrete polynomial, root,
and generated subring model `K[a^{1/p}]` and `A[a^{1/p}]`; the residue nonpower hypothesis then
identifies the latter with the normalization and supplies its DVR and weakly-unramified API.

@stack 09EX
-/

namespace Lemma_15_116_8

/- Lemma 15.116.8 (1): a residue nonpower remains a nonpower in the fraction field. -/
@[stacks 09EX "Lemma 15.116.8 (1): fraction-field nonpower"]
#check @DVR.Kummer.not_mem_powerRange

/- Lemma 15.116.8 (2): the normalization is the explicit root ring `A[a^{1/p}]`. -/
@[stacks 09EX "Lemma 15.116.8 (2): explicit normalization"]
#check @DVR.Kummer.normalization_eq_rootRing

/- Lemma 15.116.8 (3): the explicit root ring is a discrete valuation ring. -/
@[stacks 09EX "Lemma 15.116.8 (3): root ring is a DVR"]
#check @DVR.Kummer.rootRing_isDVR

/- Lemma 15.116.8 (4): the explicit root-ring extension is weakly unramified. -/
@[stacks 09EX "Lemma 15.116.8 (4): root ring is weakly unramified"]
#check @DVR.Kummer.rootRing_weaklyUnramified

#check @DVR.Kummer.IsResidueNonpower
#check @DVR.Kummer.polynomial
#check @DVR.Kummer.RootExtension
#check @DVR.Kummer.root
#check @DVR.Kummer.RootRing
#check @DVR.Kummer.polynomial_irreducible
#check @DVR.Kummer.normalization_isDVR
#check @DVR.Kummer.normalization_weaklyUnramified

end Lemma_15_116_8
