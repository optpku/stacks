module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
import StacksCheckRecall

/-!
# Definition 17.14.1 compatibility entry point

The three properties are owned on arbitrary ringed sites.  The companion neighborhood theorems
recover the pointwise formulation used for ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 17.14.1 (01C6) (1): locally free module sheaves. -/
@[stacks 01C6 "(1)"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) ↦ F.IsLocallyFree

/- Definition 17.14.1 (01C6) (2): finite locally free module sheaves. -/
@[stacks 01C6 "(2)"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) ↦ F.IsFiniteLocallyFree

/- Definition 17.14.1 (01C6) (3): finite locally free module sheaves of rank `r`. -/
@[stacks 01C6 "(3)"]
#check fun {X : RingedSpace.{u}} (r : ℕ) (F : X.Modules) ↦
  SheafOfModules.IsFiniteLocallyFreeOfRank r F

#check @SheafOfModules.IsLocallyFree.exists_neighborhood
#check @SheafOfModules.IsLocallyFree.iff_exists_neighborhood
#check @SheafOfModules.isFiniteLocallyFree_iff
#check @SheafOfModules.IsFiniteLocallyFree.of_iso
#check @SheafOfModules.IsFiniteLocallyFree.iff_of_iso
#check @SheafOfModules.IsFiniteLocallyFree.exists_neighborhood
#check @SheafOfModules.IsFiniteLocallyFree.iff_exists_neighborhood
#check @SheafOfModules.isFiniteLocallyFreeOfRank_iff
#check @SheafOfModules.IsFiniteLocallyFreeOfRank.iff_of_iso
#check @SheafOfModules.IsFiniteLocallyFreeOfRank.exists_neighborhood
#check @SheafOfModules.IsFiniteLocallyFreeOfRank.iff_exists_neighborhood
#check @SheafOfModules.IsFiniteLocallyFreeOfRank.moduleStalkIsoFree
