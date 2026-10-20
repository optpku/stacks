module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Relative dimension of morphisms with Cohen-Macaulay fibers

This module records the clopen decomposition of the source of a flat, locally finitely
presented morphism with Cohen-Macaulay fibers according to relative dimension.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat, locally finitely presented morphism with Cohen-Macaulay fibers admits a pairwise
disjoint clopen cover of its source on which the morphism has constant relative dimension. -/
theorem exists_clopen_relativeDimension_decomposition {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, Scheme.CohenMacaulay (f.fiber s)) :
    ∃ U : ℕ → X.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun d e ↦ Disjoint (U d : Set X) (U e : Set X)) ∧
        (∀ d, IsClopen (U d : Set X)) ∧
        ∀ d, RelativeDimension ((U d).ι ≫ f) d := sorry

end AlgebraicGeometry.Scheme.Hom
