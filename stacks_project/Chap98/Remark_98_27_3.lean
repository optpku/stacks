/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap98.Lemma_98_27_4_Functor
public import stacks_project.Chap98.Situation_98_27_1_Contraction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility as equality of interpolating maps

In a contraction situation, compatibility of an open-complement morphism with
an adic map of completions is uniqueness of interpolators, not extra diagram
data.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Remark 98.27.3: in Situation 98.27.1, let `V` be a locally Noetherian scheme
over `S`, and let `(Z, u', hatx)` satisfy (1)–(3): `Z` is closed in
`Points (ofOver V)`, `u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement`
is a morphism over `S`, and `hatx : completionAlong (ofOver V) Z ⟶ σ.W` is
adic in the sense `representableByAlgebraicSpaces hatx`. Compatibility (4) is
explained heuristically by a fictitious category `An_S` of analytic spaces over
`S` and a fictitious analytification functor sending a locally Noetherian
formal algebraic space `Y` to `Y^an`. For example `Spf(k[[t]])^an` is pictured
as an open unit disc and `Spec(k)^an` as a point. Forming `Y^rig` as the open
complement of the closed immersion `(Y_red)^an ⟶ Y^an`, an open immersion
`can : (Y_/Z)^rig ⟶ (Y \ Z)^an`, and an isomorphism `g^rig` for a formal
modification `g`, compatibility of `u'` and `hatx` would be the commuting
square of `can`, `(g^rig)⁻¹ ≫ hatx^an`, and `(u')^an`. Under a hoped-for
faithfulness of analytification this matches an interpolating morphism
`x' : V' ⟶ σ.X'`. Algebraically, interpolators out of a locally Noetherian
algebraic space `V'` that recover `u'` on the open complement of
`Z.preimage (Points.continuous_map f)` and `hatx'` along `completionAlong.ι`
are unique: compatibility is equality of maps, not extra diagram data. -/
@[stacks 0GID]
theorem compatibilityAsMapEquality (σ : ContractionSituation S) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W)
    (h_adic : representableByAlgebraicSpaces hatx)
    {V' : AlgebraicSpace S} [IsLocallyNoetherian V'] (f : V' ⟶ ofOver V)
    (hatx' : completionAlong V' (Z.preimage (Points.continuous_map f)) ⟶ σ.completion)
    (x₁ x₂ : V' ⟶ σ.X')
    (h_open₁ :
      AlgebraicSpace.openComplementι V' (Z.preimage (Points.continuous_map f)) ≫ x₁ =
        openComplementAlong.map f Z ≫ u' ≫ σ.openComplementι)
    (h_open₂ :
      AlgebraicSpace.openComplementι V' (Z.preimage (Points.continuous_map f)) ≫ x₂ =
        openComplementAlong.map f Z ≫ u' ≫ σ.openComplementι)
    (h_hat₁ :
      completionAlong.ι V' (Z.preimage (Points.continuous_map f)) ≫ x₁ =
        hatx' ≫ completionAlong.ι σ.X' σ.T')
    (h_hat₂ :
      completionAlong.ι V' (Z.preimage (Points.continuous_map f)) ≫ x₂ =
        hatx' ≫ completionAlong.ι σ.X' σ.T') :
    x₁ = x₂ :=
  sorry

/-- For a locally Noetherian interpolating space `V'`, the two restriction
identities for `x₁` and for `x₂` on the open complement of
`Z.preimage (Points.continuous_map f)` and along `completionAlong.ι` hold if
and only if those identities hold and `x₁ = x₂`. -/
theorem compatibilityAsMapEquality_iff (σ : ContractionSituation S) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W)
    (h_adic : representableByAlgebraicSpaces hatx)
    {V' : AlgebraicSpace S} [IsLocallyNoetherian V'] (f : V' ⟶ ofOver V)
    (hatx' : completionAlong V' (Z.preimage (Points.continuous_map f)) ⟶ σ.completion)
    (x₁ x₂ : V' ⟶ σ.X') :
    ((AlgebraicSpace.openComplementι V' (Z.preimage (Points.continuous_map f)) ≫ x₁ =
          openComplementAlong.map f Z ≫ u' ≫ σ.openComplementι ∧
        completionAlong.ι V' (Z.preimage (Points.continuous_map f)) ≫ x₁ =
          hatx' ≫ completionAlong.ι σ.X' σ.T') ∧
      (AlgebraicSpace.openComplementι V' (Z.preimage (Points.continuous_map f)) ≫ x₂ =
          openComplementAlong.map f Z ≫ u' ≫ σ.openComplementι ∧
        completionAlong.ι V' (Z.preimage (Points.continuous_map f)) ≫ x₂ =
          hatx' ≫ completionAlong.ι σ.X' σ.T')) ↔
      ((AlgebraicSpace.openComplementι V' (Z.preimage (Points.continuous_map f)) ≫ x₁ =
            openComplementAlong.map f Z ≫ u' ≫ σ.openComplementι ∧
          completionAlong.ι V' (Z.preimage (Points.continuous_map f)) ≫ x₁ =
            hatx' ≫ completionAlong.ι σ.X' σ.T') ∧
        (AlgebraicSpace.openComplementι V' (Z.preimage (Points.continuous_map f)) ≫ x₂ =
            openComplementAlong.map f Z ≫ u' ≫ σ.openComplementι ∧
          completionAlong.ι V' (Z.preimage (Points.continuous_map f)) ≫ x₂ =
            hatx' ≫ completionAlong.ι σ.X' σ.T') ∧
        x₁ = x₂) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
