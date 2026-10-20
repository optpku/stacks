/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.117.7

The Noetherian, spectrum-surjectivity, and residue-field conclusions are owned by the shared DVR
base-change leaf.

@stack 09IH
-/

/- Lemma 15.117.7 (1): the target normalization is Noetherian. -/
@[stacks 09IH "Lemma 15.117.7 (1)"]
#check @DVR.BaseChange.targetNormalization_noetherian

/- Lemma 15.117.7 (2): the induced map on spectra is surjective. -/
@[stacks 09IH "Lemma 15.117.7 (2)"]
#check @DVR.BaseChange.spectrum_comap_surjective

/- Lemma 15.117.7 (3): the corresponding residue-field extensions are finitely generated. -/
@[stacks 09IH "Lemma 15.117.7 (3)"]
#check @DVR.BaseChange.residueField_finiteType
