module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Discriminants of finite locally free scheme morphisms

This file defines the discriminant locus through the trace pairing on residue-field fibres and
records its relation to étaleness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The discriminant locus of a finite locally free scheme morphism is the set of target points
where the trace pairing on the global-sections algebra of the residue-field fibre is degenerate. -/
def discriminantLocus (f : X ⟶ Y) [IsFiniteLocallyFree f] : Set Y :=
  {y | ¬(Algebra.traceForm (Y.residueField y) (f.fiberGlobalSections y)).Nondegenerate}

/-- A point belongs to the discriminant locus of a finite locally free scheme morphism exactly
when the trace pairing on its residue-field fibre is degenerate. -/
theorem mem_discriminantLocus (f : X ⟶ Y) [IsFiniteLocallyFree f] (y : Y) :
    y ∈ f.discriminantLocus ↔
      ¬(Algebra.traceForm (Y.residueField y) (f.fiberGlobalSections y)).Nondegenerate := sorry

/-- A finite locally free morphism of schemes is étale if and only if its discriminant locus is
empty. -/
theorem etale_iff_discriminantLocus_eq_empty (f : X ⟶ Y) [IsFiniteLocallyFree f] :
    Etale f ↔ f.discriminantLocus = ∅ := sorry

end AlgebraicGeometry.Scheme.Hom
