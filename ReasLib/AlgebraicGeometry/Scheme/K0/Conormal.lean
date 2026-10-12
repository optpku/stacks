/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Z X : Scheme.{u}}

/-- The conormal sheaf of a closed immersion is finite locally free, and its
vector-bundle `K₀` class is the `K₀`-pullback of a class on the target. -/
def ConormalClassExtends (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  ∃ hC : Scheme.Modules.IsFiniteLocallyFree (conormalSheaf i),
    ∃ alpha : Scheme.K0 X,
      Scheme.K0.pullback i alpha =
        Scheme.VectorBundleK0.toK0 Z
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Z.Modules)
            ⟨conormalSheaf i, hC⟩)

end AlgebraicGeometry.Scheme.Hom
