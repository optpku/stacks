/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Situation_85_24_1_LocallyGiven
import StacksCheckRecall

/-!
# Situation 85.24.1

A locally given derived glueing datum on a ringed site is the bundled owner
`SheafOfModules.Derived.LocallyGiven`, specialized to the ringed site's ring sheaf.
-/

@[expose]
public section

open CategoryTheory

universe u v w z uB vB

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}]

/- Situation 85.24.1: a ringed site `X`, a functor `u : B ⥤ X`, objects
`E_U` of `ModuleDerived (X.localization (u.obj U))`, and isomorphisms
`ρ_a : restrictionDerived (u.map a) (E_U) ≅ E_V` compatible with composition. -/
@[stacks 0DC9] #check
  (SheafOfModules.Derived.LocallyGiven X.structureSheaf
    (abelianOver := fun U =>
      (RingedSite.Hom.localizedModuleCatAbelian U :
        Abelian (RingedSite.ModuleCat.{z} (X.localization U)))) :
    (B : Type uB) → [Category.{vB} B] → Type (max u v w (z + 1) uB vB))
