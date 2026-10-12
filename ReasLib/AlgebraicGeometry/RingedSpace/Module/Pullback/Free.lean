/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of free module sheaves on ringed spaces

This leaf specializes the ringed-site free-pullback comparison to morphisms of ringed spaces.
The specialization hides the site-level finality and sheafification parameters from downstream
statements.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}}

set_option maxHeartbeats 800000 in
/-- Pullback along a morphism of ringed spaces carries the free module sheaf on `I` to the free
module sheaf on the same indexing type. -/
@[stacks 03DF "free module sheaf pullback"]
noncomputable def pullbackFreeIso (f : X ⟶ Y) (I : Type u) :
    (pullback f).obj (SheafOfModules.free I : Y.Modules) ≅
      (SheafOfModules.free I : X.Modules) :=
  SheafOfModules.pullbackObjFreeIso (toRingCatSheafHom f) I

end AlgebraicGeometry.RingedSpace.Hom
