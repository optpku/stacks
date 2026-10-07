module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {X : RingedSpace.{u}}

/- Definition 17.11.1 (01BN): for a sheaf of `𝒪_X`-modules on a ringed space, being of finite
presentation is the canonical predicate `SheafOfModules.IsFinitePresentation`, defined upstream by
local finite presentations on a covering family of opens and matching the neighbourhood
formulation in the text. -/
@[stacks 01BN]
#check (fun F : X.Modules => F.IsFinitePresentation)

/- The reusable comparison interface transports the property across an explicit module-sheaf
isomorphism without exposing a chosen local presentation. -/
#check @SheafOfModules.IsFinitePresentation.of_iso
#check @SheafOfModules.IsFinitePresentation.iff_of_iso

#check fun {F G : X.Modules} (e : F ≅ G) [F.IsFinitePresentation] ↦
  (SheafOfModules.IsFinitePresentation.of_iso (M := F) (N := G) e :
    G.IsFinitePresentation)
