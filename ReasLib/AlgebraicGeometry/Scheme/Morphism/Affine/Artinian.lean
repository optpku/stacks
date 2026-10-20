/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine morphisms from Artinian schemes

A finite discrete scheme is affine, and every open subscheme of it is again finite and discrete.
Consequently every morphism from such a scheme is affine. This applies in particular to Artinian
schemes and to spectra of Artinian rings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every morphism from a finite discrete scheme is affine. -/
instance (priority := 100) isAffineHom_of_finite_discrete_source
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Finite X] [DiscreteTopology X] : IsAffineHom f := by
  constructor
  intro U _
  -- Local instance justification (proof-local temporary data): the inverse-image open subscheme is finite.
  letI : Finite (f ⁻¹ᵁ U) := Finite.of_injective Subtype.val Subtype.val_injective
  -- Local instance justification (proof-local temporary data): the inverse-image open subscheme is discrete.
  letI : DiscreteTopology (f ⁻¹ᵁ U) := (f ⁻¹ᵁ U).ι.isOpenEmbedding.discreteTopology
  change IsAffine (f ⁻¹ᵁ U)
  infer_instance

/-- Every morphism from the spectrum of an Artinian ring is affine. -/
@[stacks 01SI]
theorem isAffineHom_of_artinianSpec
    {S : Scheme.{u}} {A : CommRingCat.{u}} [IsArtinianRing A]
    (f : Spec A ⟶ S) : IsAffineHom f :=
  isAffineHom_of_finite_discrete_source f

end AlgebraicGeometry
