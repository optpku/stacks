/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Descent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a locally finite type morphism and a finite-type quasicoherent module, the locus
where the module is flat over the base is open in every scheme-theoretic fibre. -/
@[stacks 05M9]
theorem isOpen_flatOverAt_fiber {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    IsOpen ((f.fiberι s) ⁻¹' {x : X | flatOverAt F f x}) := sorry

/-- The locus in the fibre over `s` where `ℱ` is not flat over the base. -/
def fiberNonflatLocus {X S : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ S) (s : S) : Set (f.fiber s) :=
  {x | ¬ flatOverAt ℱ f (f.fiberι s x)}

/-- A point belongs to the fibrewise nonflat locus exactly when relative flatness fails at
its image in the total space. -/
theorem mem_fiberNonflatLocus {X S : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ S) (s : S) (x : f.fiber s) :
    x ∈ fiberNonflatLocus ℱ f s ↔ ¬ flatOverAt ℱ f (f.fiberι s x) := sorry

/-- The nonflat locus in each fibre is closed for a finite-type quasicoherent module over a
locally finite-type morphism. -/
theorem isClosed_fiberNonflatLocus {X S : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S) :
    IsClosed (fiberNonflatLocus ℱ f s) := sorry

end AlgebraicGeometry.Scheme.Modules
