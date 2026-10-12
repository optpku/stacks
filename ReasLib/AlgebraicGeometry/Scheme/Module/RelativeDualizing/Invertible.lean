/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion.FreeNeighborhood

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/-- For a quasi-finite flat morphism of Noetherian schemes, a relative dualizing sheaf is
invertible exactly when its pullback to every scheme-theoretic fiber is invertible. -/
theorem invertible_iff_fiberwise
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf) :
    Scheme.Modules.Invertible W.module.obj ↔
      ∀ x : X,
        Scheme.Modules.Invertible
          ((Scheme.Modules.pullback (f.fiberι x)).obj W.module.obj) := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
