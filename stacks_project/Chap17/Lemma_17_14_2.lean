/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 17.14.2 (01C7): a locally free module sheaf on a ringed space is quasicoherent. -/
@[stacks 01C7]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsLocallyFree] ↦
  (SheafOfModules.IsLocallyFree.isQuasicoherent F : F.IsQuasicoherent)

#check @SheafOfModules.IsLocallyFree.isQuasicoherent
