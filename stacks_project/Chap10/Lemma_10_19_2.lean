/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import StacksCheckRecall

/-!
# Surjectivity on spectra and units

@stack 0B7C

Lemma 10.19.2 is the composition of the local-map and unit-map criteria
recalled below.
-/

@[expose] public section

@[stacks 0B7C "local-map criterion"]
#check @IsLocalHom.of_comap_surjective

@[stacks 0B7C "unit-map equivalence"]
#check @isUnit_map_iff
