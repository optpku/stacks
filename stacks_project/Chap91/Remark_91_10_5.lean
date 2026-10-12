/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Remark_91_10_5_Trivialized
public import stacks_project.Chap91.«91_10_5_1»
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite

/- Remark 91.10.5 (1): a first-order thickening `π : O' ⟶ O` of a ringed topos `(Sh(C), O)` is
trivial when it admits a left inverse. -/
@[stacks 08MG] #check @FirstOrderThickening.IsTrivial

/- Remark 91.10.5 (2): a trivialization of a first-order thickening is a chosen left inverse
`σ : O ⟶ O'`. -/
@[stacks 08MG] #check @FirstOrderThickening.IsTrivialization

/- Remark 91.10.5 (3): given a trivialization, the projection splits as sheaves of algebras
`O' ≅ trivSqZeroExt O I` on `C`. -/
@[stacks 08MG] #check splittingIso

/- Remark 91.10.5 (4): conversely, an algebra splitting `O' ≅ trivSqZeroExt O I` determines a
retraction of the projection. -/
@[stacks 08MG] #check @FirstOrderThickening.splitEpiOfIso

/- Remark 91.10.5 (5): morphisms of trivialized first-order thickenings of `O` correspond to
morphisms of `O`-modules. -/
@[stacks 08MG] #check @FirstOrderThickening.homEquiv
