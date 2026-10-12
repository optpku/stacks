/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Noetherian
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.Algebra.Module.Graded.DegreeZero
public import ReasLib.RingTheory.GradedAlgebra.Irrelevant
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite graded pieces over degree zero

This leaf owns the reusable finiteness interface needed by Hilbert and Grothendieck-class
arguments. A graded module piece is an `R`-submodule of the ambient module; the degree-zero
action is supplied by `GradedModule.zeroPieceModule`.
-/

@[expose] public section

universe u v w

namespace GradedModule

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]

/-- A finite graded `S`-module has finitely generated degree pieces over its degree-zero ring. -/
@[stacks 00K0 "finite graded piece over degree zero"]
theorem finitePiece [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    (n : ℤ) : Module.Finite (𝒜 0) (ℳ n) := sorry

end GradedModule

namespace GradedAlgebra

/-- A Noetherian nonnegatively graded algebra is finite type over its degree-zero component. -/
@[stacks 00JW "Noetherian graded algebra is finite type"]
theorem finiteType_of_isNoetherian
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜] [IsNoetherianRing S] :
    Algebra.FiniteType (𝒜 0) S := sorry

end GradedAlgebra

namespace HomogeneousIdeal

variable {S : Type u} [CommRing S]
variable {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A nonnegatively graded ring is finite type over its
degree-zero part exactly when its irrelevant ideal is finitely generated. -/
@[stacks 00JW "finite-type criterion"]
theorem finiteType_iff_irrelevant_fg :
    Algebra.FiniteType (𝒜 0) S ↔ 𝒜₊.toIdeal.FG := sorry

/-- A nonnegatively graded ring is Noetherian exactly when its
degree-zero part is Noetherian and its irrelevant ideal is finitely generated. -/
@[stacks 00JW "Noetherian criterion"]
theorem isNoetherianRing_iff_degreeZero_and_irrelevant_fg :
    IsNoetherianRing S ↔ IsNoetherianRing (𝒜 0) ∧ 𝒜₊.toIdeal.FG := sorry

end HomogeneousIdeal
