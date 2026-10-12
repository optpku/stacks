/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents

/-!
# Normalization and irreducible components

The normalization of a scheme with locally finite irreducible components is the coproduct of
the normalizations of its reduced irreducible-component subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The normalization of a scheme whose quasi-compact opens have finitely many irreducible
components is the coproduct of the normalizations of its reduced irreducible-component
subschemes, compatibly with the canonical morphisms to the scheme. -/
theorem normalizationIsoCoproductIrreducibleComponentNormalizations
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    let componentScheme : irreducibleComponents X → Scheme.{u} :=
      X.irreducibleComponentSubscheme
    ∃ e :
        (∐ fun Z : irreducibleComponents X ↦
            (componentScheme Z).normalization) ≅ X.normalization,
      Limits.Sigma.desc (fun Z : irreducibleComponents X ↦
          (componentScheme Z).normalizationTo ≫
            X.irreducibleComponentSubschemeι Z) =
        e.hom ≫ X.normalizationTo := sorry

end

end AlgebraicGeometry.Scheme
