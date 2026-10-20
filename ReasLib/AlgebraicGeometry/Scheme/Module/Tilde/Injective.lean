module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.NoetherianSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.tilde

/-- There exists an affine scheme with Noetherian underlying space and an injective
module whose associated sheaf has nonvanishing first cohomology on a quasi-compact
open subset. -/
theorem exists_injective_qcOpen_h1_ne_zero :
    ∃ (A : CommRingCat.{u}) (I : ModuleCat.{u} A) (U : Opens (Spec A)),
      Module.Injective A I ∧
        NoetherianSpace (Spec A) ∧
        IsCompact (U : Set (Spec A)) ∧
          ¬ IsZero (RingedSpace.moduleCohomologyOnOpen (tilde I) 1 U) := sorry

end AlgebraicGeometry.tilde
