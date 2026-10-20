/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Relative normalization along universally closed morphisms

The pushforward structure algebra of a quasi-compact quasi-separated universally
closed morphism is integral. Its relative spectrum is the relative normalization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The pushforward structure algebra of a quasi-compact, quasi-separated,
universally closed morphism of algebraic spaces is integral. -/
instance instIsIntegral_pushforwardStructureQcAlgebra
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] :
    QcAlgebraUnder.IsIntegral (pushforwardStructureQcAlgebra f) :=
  sorry

/-- If `f` is quasi-compact, quasi-separated and universally closed, then the
inclusion of the integral closure of `𝒪_Y` in `f_* 𝒪_X` is an isomorphism. -/
instance instIsIso_integralClosureAlgebra_inclusion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] :
    IsIso (integralClosureAlgebra_inclusion f) :=
  sorry

/-- For a quasi-compact, quasi-separated, universally closed morphism `f : X ⟶ Y`,
the canonical factorization through the relative spectrum of `f_* 𝒪_X` exhibits
the relative normalization of `Y` in `X`. -/
theorem isNormalization_toPushforwardRelativeSpec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] :
    IsNormalization f (toPushforwardRelativeSpec f)
      (relativeSpecπ (pushforwardStructureQcAlgebra f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
