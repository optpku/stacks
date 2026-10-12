/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Situation_85_24_1_LocallyGiven
import StacksCheckRecall

/-!
# Situation 85.24.1

A locally given derived glueing datum on a ringed site is the bundled owner
`RingedSite.ModuleDerived.LocallyGiven`.
-/

@[expose]
public section

open RingedSite.ModuleDerived

/- Situation 85.24.1: a ringed site `X`, a functor `u : B ⥤ X`, objects
`E_U` of `ModuleDerived (X.localization (u.obj U))`, and isomorphisms
`ρ_a : restrictionDerived (u.map a) (E_U) ≅ E_V` compatible with composition. -/
@[stacks 0DC9] #check @LocallyGiven
