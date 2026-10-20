/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure
public import ReasLib.RingTheory.KrullDimension.DimensionLEOne
import StacksCheckRecall

/-!
# Integral closures over one-dimensional Noetherian domains

@stack 09IG
-/

@[expose] public section

/- Lemma 10.120.18 (1): Krull dimension one supplies the reusable
dimension-at-most-one hypothesis, and the finite integral closure is Dedekind. -/
@[stacks 09IG "(1), dimension bridge"]
#check @Ring.dimensionLEOne_of_ringKrullDim_eq_one

@[stacks 09IG "(1), Dedekind integral closure"]
#check @FractionRing.IntegralClosure.isDedekind_of_finite_extension

/- Lemma 10.120.18 (2): the induced map on prime spectra is surjective. -/
@[stacks 09IG "(2), integral spectrum surjectivity"]
#check @FractionRing.IntegralClosure.spectrum_comap_surjective

/- Lemma 10.120.18 (3): every prime fiber is finite. -/
@[stacks 09IG "(3), finite prime fibers"]
#check @FractionRing.IntegralClosure.primesOver_finite_of_dim_one

/- Lemma 10.120.18 (4): every induced residue-field extension is finite. -/
@[stacks 09IG "(4), finite residue-field extensions"]
#check @FractionRing.IntegralClosure.residueField_finite_of_dim_one

@[stacks 09IG "(4), selected residue-field algebra"]
#check @Ideal.ResidueField.algebraOfLiesOver
