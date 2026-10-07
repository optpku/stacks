module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.Derived

/- Lemma 36.7.2. For a quasi-compact, quasi-separated, flat morphism `f : X ⟶ Y`,
ambient derived pushforward followed by `RQ_Y` is naturally isomorphic to `RQ_X` followed by
the right-derived quasicoherent pushforward `Φ`. -/
@[stacks 08D8]
theorem pushforwardCoherator_isomorphic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat f] :
    IsIsomorphic
      (RingedSpace.moduleDerivedPushforward f.toShHom ⋙ coherator Y)
      (coherator X ⋙ pushforward f) := by
  sorry

end AlgebraicGeometry.Scheme.QCoh.Derived
