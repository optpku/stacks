module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.Neighborhood
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

/-!
# Lemma 17.11.7

The shared owner first treats an arbitrary finite basis type.  This file checks its
source-faithful specialization to the standard rank-`r` basis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.IsFinitePresentation

variable {X : RingedSpace.{u}}
variable (F : X.Modules) [F.IsFinitePresentation]
variable (x : X) (r : ℕ)
variable (h : Nonempty
  (RingedSpace.stalkModuleCat F x ≅
    ModuleCat.freeFin (X.presheaf.stalk x) r))

/- Lemma 17.11.7 (0B8J): a free rank-`r` stalk of a finitely presented module sheaf extends to
a free rank-`r` trivialization on a neighborhood. -/
@[stacks 0B8J]
#check
  (CommRing.existsNeighborhoodFreeOfStalkIsoFin F x r h :
    ∃ (U : Opens X) (_ : x ∈ U),
      Nonempty (F.over U ≅ SheafOfModules.freeFin r))

end SheafOfModules.IsFinitePresentation
