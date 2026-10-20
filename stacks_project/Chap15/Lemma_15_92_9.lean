/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.LocalizationAway
import StacksCheckRecall

/-!
# Iterated localization-away derived internal Hom

@stack 0A6C

The reusable owner first identifies `A_f[0] ⊗ᴸ_A A_g[0]` with `A_{fg}[0]` and then applies the
source-order derived internal-Hom currying isomorphism.  The closed structure and fixed-right
tensor model remain explicit because the ambient derived category does not select either one.
-/

@[expose] public section

/- Lemma 15.92.9 (0A6C):
`RHom_A(A_f, RHom_A(A_g, K)) ≅ RHom_A(A_{fg}, K)`. -/
@[stacks 0A6C "iterated localization-away derived internal Hom"]
#check @CategoryTheory.DerivedCategory.localizationAwayT_mulIso

/- The source comparison is the canonical product formula
`A_f[0] ⊗ᴸ_A A_g[0] ≅ A_{fg}[0]`. -/
@[stacks 0A6C "derived tensor of principal localizations"]
#check @CategoryTheory.DerivedCategory.LocalizationAway.tensorIso
