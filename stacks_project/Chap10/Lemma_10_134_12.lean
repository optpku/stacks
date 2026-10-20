/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.LocalizationAway
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.134.12

@stack 08JZ

The source statement is a canonical recall of the localization-away comparison
for naive cotangent complexes.  ReasLib owns both the presentation-level map
and the self-presentation specialization, so no chapter-local tensor-model or
coordinate API is exported here.
-/

open scoped TensorProduct

/- Lemma 10.134.12 [stacks 08JZ]: for an away-localization `T` of an
`R`-algebra `S`, the literal scalar extension of `NL{S⁄R}` maps to `NL{T⁄R}`
by a morphism that becomes an isomorphism in the homotopy category.  The
explicit two-term tensor model is a canonically isomorphic normalization used
to construct that map. -/
@[stacks 08JZ]
#check @Algebra.NaiveCotangent.LocalizationAway.comparison_isIso

#check @Algebra.Extension.NaiveCotangent.BaseChange.scalarExtension
#check @Algebra.Extension.NaiveCotangent.BaseChange.tensorModel
#check @Algebra.Extension.NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
#check @Algebra.NaiveCotangent.LocalizationAway.comparison
