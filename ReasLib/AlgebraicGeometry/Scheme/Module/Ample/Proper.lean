/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections.Truncation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.FiniteGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.OverSpec

/-!
# Ample modules on proper schemes

This file records finite generation of section rings and truncated twisted sections, together
with eventual vanishing of positive cohomology, for ample invertible modules on proper schemes
over Noetherian affine bases.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsAmple

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- The canonical section ring of an ample invertible module on a proper scheme over a
Noetherian affine base is a finite-type algebra over the base ring. -/
@[stacks 0B5T "finite-type ample section ring"]
theorem sectionRing_finiteType
    (L : X.Modules) [L.Invertible] [IsAmple L] :
    Algebra.FiniteType R (Scheme.Hom.sectionRingAlg f L) := sorry

/-- Positive-degree cohomology of a coherent module twisted by sufficiently large powers of an
ample invertible module vanishes on a proper scheme over a Noetherian affine base. -/
@[stacks 0B5T "eventual vanishing for ample twists"]
theorem twistCohomology_eventually_isZero
    (L F : X.Modules) [L.Invertible] [IsAmple L] [F.IsCoherent]
    (p : ℕ) (hp : 0 < p) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      IsZero (Scheme.Hom.cohomology f (F ⊗ L ^⊗ d) p) := sorry

include f

/-- Every lower truncation of the canonically acted-on twisted global sections of a coherent
module is finite over the section ring of an ample invertible module on a proper scheme over a
Noetherian affine base. -/
@[stacks 0B5T "finite lower truncations of twisted global sections"]
theorem truncatedSections_finite
    (L F : X.Modules) [L.Invertible] [IsAmple L] [F.IsCoherent]
    (k : ℤ) :
    Module.Finite (RingedSpace.GradedSections.ring L)
      (RingedSpace.GradedSections.truncatedTwisted L F k) := sorry

end AlgebraicGeometry.Scheme.Modules.IsAmple
