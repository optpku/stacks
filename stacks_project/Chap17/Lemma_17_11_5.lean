module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

/-!
# Lemma 17.11.5

The source statement is the ringed-space specialization of the generic ringed-site pullback
theorem.  Canonical opens-site instances keep sheafification infrastructure off this surface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}}
variable (f : X ⟶ Y) (G : Y.Modules) [G.IsFinitePresentation]

/- Lemma 17.11.5 (01BQ): pullback of a finitely presented module sheaf along a morphism of
ringed spaces is finitely presented. -/
@[stacks 01BQ]
#check
  (inferInstance : ((pullback f).obj G).IsFinitePresentation)

end AlgebraicGeometry.RingedSpace.Hom
