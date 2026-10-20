/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian

/-!
# Curve degree across irreducible components

This file records the decomposition of the degree of a finite locally free module on a proper
scheme of dimension at most one into contributions from its one-dimensional irreducible
components.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.curveDegree

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- The degree of a finite locally free module on a proper scheme of dimension at most one is the
sum of its degrees on the reduced one-dimensional irreducible-component subschemes, weighted by
their multiplicities. -/
@[stacks 0AYW]
theorem eq_sum_irreducibleComponents
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
    [IsFiniteLocallyFreeOfRank n ℰ] :
    -- Local instance justification (proof-local temporary data): properness over a field gives
    -- finite type, so the canonical finite-type theorem supplies global Noetherianity.
    let _ : IsNoetherian X := Scheme.Hom.FiniteType.isNoetherian f
    -- Local instance justification (proof-local temporary data): a Noetherian space has finitely
    -- many irreducible components.
    let _ : Finite (irreducibleComponents X) :=
      AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
    -- Local instance justification (noncanonical choice): the finite component type is enumerated
    -- only in order to form the finite sum.
    let _ : Fintype (irreducibleComponents X) := Fintype.ofFinite (irreducibleComponents X)
    curveDegree f hdim ℰ n =
      Finset.sum
        ((Finset.univ.filter fun Z : irreducibleComponents X ↦
          topologicalKrullDim (X.irreducibleComponentSubscheme Z) = 1).attach) fun Z ↦
        (X.irreducibleComponentMultiplicity Z.1 : ℤ) *
          curveDegree (X.irreducibleComponentSubschemeι Z.1 ≫ f)
            (((Finset.mem_filter.mp Z.2).2).le)
            ((Scheme.Modules.pullback (X.irreducibleComponentSubschemeι Z.1)).obj ℰ) n := sorry

end AlgebraicGeometry.Scheme.Modules.curveDegree
