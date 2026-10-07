module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Structure

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The largest open of a scheme on which a module becomes invertible after pullback. -/
noncomputable def invertibleLocus (F : X.Modules) : X.Opens :=
  ⨆ U : { U : X.Opens // Invertible ((pullback U.ι).obj F) }, U.1

/-- A point lies in `invertibleLocus F` exactly when `F` is invertible on some open
neighborhood of that point. -/
theorem mem_invertibleLocus (F : X.Modules) (x : X) :
    x ∈ invertibleLocus F ↔
      ∃ U : X.Opens, x ∈ U ∧ Invertible ((pullback U.ι).obj F) := sorry

end AlgebraicGeometry.Scheme.Modules
