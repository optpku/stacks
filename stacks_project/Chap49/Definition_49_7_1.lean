module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Definition 49.7.1: Let `f : Y ⟶ X` be a locally finite type morphism of schemes. The
Kähler different is the zeroth Fitting ideal sheaf of `Ω[f.toShHom]`. -/
@[stacks 0BVW] #check
  (AlgebraicGeometry.Scheme.Hom.kaehlerDifferent :
    {Y X : Scheme.{u}} → (f : Y ⟶ X) → [LocallyOfFiniteType f] → Y.IdealSheafData)

end AlgebraicGeometry.Scheme.Hom
