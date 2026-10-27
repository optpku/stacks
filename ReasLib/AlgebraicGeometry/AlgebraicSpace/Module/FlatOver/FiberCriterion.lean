/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Fiberwise
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

/-!
# Criterion of flatness by fibres over a Noetherian base

Relative flatness of a coherent module on locally Noetherian algebraic spaces can be
tested by flatness over the base and on its fibres at points of the module's support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a coherent quasi-coherent module on locally Noetherian algebraic spaces
`X ⟶ Y ⟶ Z`, at a point of its support, flatness over `Z` together with flatness of its
fibre restriction over the fibre of `Y` is equivalent to flatness of `Y` over `Z` at the
image point together with flatness of the module over `Y`. -/
@[stacks 0APR]
theorem flatOverAt_and_fiber_iff {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent]
    (x : Points X) (h_stalk : x ∈ moduleSupport F) :
    (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt_field F f h x) ↔
      (FlatAt h (Points.map f x) ∧ flatOverAt F f x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
