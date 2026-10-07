module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support

/-!
# Dimension of the fibrewise support of a scheme module

This module defines the Krull dimension of the support of a module after
pullback to a scheme-theoretic fibre.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The dimension of the support of the pullback of `F` to the fibre of `f`
over `s`. -/
noncomputable def fiberSupportDimension {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (s : S) : WithBot ℕ∞ :=
  topologicalKrullDim (moduleSupport ((Scheme.Modules.pullback (f.fiberι s)).obj F))

/-- `fiberSupportDimension f F s` is the topological Krull dimension of the
support of `F` on the fibre over `s`. -/
theorem fiberSupportDimension_def {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (s : S) :
    fiberSupportDimension f F s =
      topologicalKrullDim (moduleSupport ((Scheme.Modules.pullback (f.fiberι s)).obj F)) := sorry

end AlgebraicGeometry.Scheme.Modules
