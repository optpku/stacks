/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Trace

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe u

/- Exercise 111.48.5 (1): the trace map `Ext^i(E, E) ⟶ H^i(X, 𝒪_X)` for a finite locally
free `𝒪_X`-module `E` on a ringed space `X`, realized as `Ext^i(𝒪_X, 𝒪_X)`. -/
@[stacks 0DD5] #check
  (AlgebraicGeometry.RingedSpace.Module.Trace.ext_end :
    ∀ {X : RingedSpace.{u}} [HasExt X.Modules]
      (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
      Ext E E i →+
        Ext (SheafOfModules.unit X.ringCatSheaf)
          (SheafOfModules.unit X.ringCatSheaf) i)

/- Exercise 111.48.5 (2): the generalized trace map `Ext^i(E, E ⊗ F) ⟶ H^i(X, F)` for any
𝒪_X-module `F`, realized as `Ext^i(𝒪_X, F)`. -/
@[stacks 0DD5] #check
  (AlgebraicGeometry.RingedSpace.Module.Trace.ext :
    ∀ {X : RingedSpace.{u}} [HasExt X.Modules]
      (E F : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
      Ext E (E ⊗ F) i →+
        Ext (SheafOfModules.unit X.ringCatSheaf) F i)
