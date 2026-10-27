/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Making a map of quasi-coherent modules vanish on a closed subscheme

Over an affine base, vanishing of a quasi-coherent map after quasi-compact base change
is witnessed by a closed subscheme of the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Let `X` be an algebraic space over an affine scheme `S`, and let `u : ℱ ⟶ 𝒢`
be a morphism of quasi-coherent modules with `𝒢` flat over `S`. If the pullback of `u`
along a quasi-compact scheme morphism `g : T ⟶ S` vanishes, then there is a closed
subscheme of `S` through which `g` factors and on which the pullback of `u` vanishes. -/
@[stacks 083K]
theorem exists_closedImmersion_of_baseChangeMap_eq_zero
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (hG_flat : flatOver 𝒢 (SchemeRealization.toBase X)) (u : ℱ ⟶ 𝒢)
    {T : Scheme.{u}} (g : T ⟶ S) [AlgebraicGeometry.QuasiCompact g]
    (hu : baseChangeMap (SchemeRealization.toBase X)
      (ofOverHomMk g (Category.comp_id g)) u = 0) :
    ∃ Z : Over S, AlgebraicGeometry.IsClosedImmersion Z.hom ∧
      Nonempty (Over.mk g ⟶ Z) ∧
        baseChangeMap (SchemeRealization.toBase X)
          (ofOverHomMk Z.hom (Category.comp_id Z.hom)) u = 0 :=
  sorry

/-- Let `X` be an algebraic space over an affine scheme `S`, and let `u : ℱ ⟶ 𝒢`
be a morphism of quasi-coherent modules with `𝒢` flat over `S`. Suppose `ℱ` has finite
type and quasi-compact scheme-theoretic support. If the pullback of `u` along a
quasi-compact scheme morphism `g : T ⟶ S` vanishes, then there is a finitely presented
closed subscheme of `S` through which `g` factors and on which the pullback of `u`
vanishes. -/
@[stacks 083K]
theorem exists_closedImmersion_of_baseChangeMap_eq_zero_of_finitePresentation
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [ℱ.IsFiniteType]
    [IsQuasiCompact (schemeTheoreticSupport ℱ).X]
    (hG_flat : flatOver 𝒢 (SchemeRealization.toBase X)) (u : ℱ ⟶ 𝒢)
    {T : Scheme.{u}} (g : T ⟶ S) [AlgebraicGeometry.QuasiCompact g]
    (hu : baseChangeMap (SchemeRealization.toBase X)
      (ofOverHomMk g (Category.comp_id g)) u = 0) :
    ∃ Z : Over S,
      (AlgebraicGeometry.IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom) ∧
        Nonempty (Over.mk g ⟶ Z) ∧
          baseChangeMap (SchemeRealization.toBase X)
            (ofOverHomMk Z.hom (Category.comp_id Z.hom)) u = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
