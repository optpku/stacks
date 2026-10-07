module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {X : RingedSpace.{u}}
variable [(SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent]

/- Lemma 17.12.5 (01BZ): if the structure module is coherent, an `𝒪_X`-module is coherent
exactly when it is finitely presented. -/
@[stacks 01BZ]
#check
  (SheafOfModules.IsCoherent.iff_finitePresentation (R := X.ringCatSheaf) :
    ∀ F : X.Modules, F.IsCoherent ↔ F.IsFinitePresentation)
