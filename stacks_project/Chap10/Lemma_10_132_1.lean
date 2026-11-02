/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Kähler de Rham base change

Lemma 10.132.1 is recalled through the degreewise canonical comparison,
its differential compatibility, and its formula on basic forms.

@stack 0H8Y
-/

@[stacks 0H8Y "base-change derivation"]
#check @KaehlerDifferential.DeRham.baseChangeDerivation
@[stacks 0H8Y "degreewise canonical isomorphism"]
#check @KaehlerDifferential.DeRham.baseChangeTermEquiv
@[stacks 0H8Y "compatibility with the de Rham differential"]
#check @KaehlerDifferential.DeRham.baseChangeTermEquiv_d
@[stacks 0H8Y "canonical comparison on basic forms"]
#check @KaehlerDifferential.DeRham.baseChangeTermEquiv_basic
@[stacks 0H8Y "canonical isomorphism of de Rham complexes"]
#check @KaehlerDifferential.DeRham.exists_complex_baseChange
@[stacks 0H8Y "base-change family"]
#check @KaehlerDifferential.DeRham.baseChange
@[stacks 0H8Y "descent comparison"]
#check @KaehlerDifferential.DeRham.baseChange_descends
@[stacks 0H8Y "square-zero transport"]
#check @KaehlerDifferential.DeRham.baseChange_squaresToZero
@[stacks 0H8Y "formula transport"]
#check @KaehlerDifferential.DeRham.baseChange_satisfiesFormula
@[stacks 0H8Y "differential transport"]
#check @KaehlerDifferential.DeRham.baseChange_isDifferential

#print axioms KaehlerDifferential.DeRham.baseChangeDerivation
#print axioms KaehlerDifferential.DeRham.baseChange
#print axioms KaehlerDifferential.DeRham.baseChangeTermEquiv
