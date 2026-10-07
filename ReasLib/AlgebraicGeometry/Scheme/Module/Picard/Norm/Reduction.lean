module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm
import Mathlib.Tactic.CrossRefAttribute

/-!
# Norms for reduction morphisms

Existence of prime-power norms for the reduction of a Noetherian scheme in prime
characteristic.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- In prime characteristic, the reduction of a Noetherian scheme admits a finite-morphism
norm of positive prime-power degree. -/
@[stacks 0BDZ]
theorem exists_norm_reduction (X : Scheme.{u}) (p : ℕ) [IsNoetherian X]
    [Fact p.Prime] [IsCharP X p] :
    ∃ e : ℕ, 0 < e ∧ ∃ N : FiniteMorphismNorm (reductionι X),
      IsFiniteMorphismNorm (reductionι X) (p ^ e) N := sorry

end AlgebraicGeometry.Scheme
