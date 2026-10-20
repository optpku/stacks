module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Proper coherent cohomology

This leaf owns the finite-generation statement for cohomology of coherent
scheme modules over a Noetherian affine base.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Cohomology of a coherent module is finite over a Noetherian affine base under a proper
morphism to that base.  The module is the canonical restriction-of-scalars object owned by
`Scheme.Hom.cohomology`. -/
@[stacks 02O6, instance]
theorem cohomologyFinite
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite A (cohomology f F i) := sorry

end AlgebraicGeometry.Scheme.Hom
