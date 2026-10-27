/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.ZeroFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Vanishing functor under proper support

For a locally finitely presented morphism, the vanishing functor of a module map
with finitely presented, relatively flat target of proper support is an algebraic
space with closed-immersion structural morphism. That morphism is finitely presented
when the source module is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

namespace zeroOverSFunctor

/-- For a locally finitely presented morphism, a module map with finitely presented,
relatively flat target of proper support has an algebraic-space vanishing functor. -/
theorem isAlgebraicSpace_of_properSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (u : ℱ ⟶ 𝒢) :
    IsAlgebraicSpace (zeroOverSFunctor f u) :=
  sorry

/-- For a locally finitely presented morphism, a module map with finitely presented,
relatively flat target of proper support has a closed-immersion vanishing locus. -/
theorem isClosedImmersion_toB_of_properSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (u : ℱ ⟶ 𝒢)
    [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  sorry

/-- For a locally finitely presented morphism, a map from a finite-type module to a
finitely presented, relatively flat module of proper support has a finitely presented
vanishing locus over the base. -/
theorem finitePresentation_toB_of_properSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (u : ℱ ⟶ 𝒢)
    [ℱ.IsFiniteType] [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  sorry

/-- Relative flatness, finite presentation, and proper support of the target module
give the vanishing functor its algebraic-space property over a locally finitely
presented morphism. -/
instance instIsAlgebraicSpaceOfProperSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    [Fact (flatOver 𝒢 f)] (u : ℱ ⟶ 𝒢) :
    IsAlgebraicSpace (zeroOverSFunctor f u) :=
  isAlgebraicSpace_of_properSupport f (Fact.out : flatOver 𝒢 f) u

/-- Relative flatness, finite presentation, and proper support of the target module
make the vanishing locus a closed immersion over a locally finitely presented morphism. -/
instance instIsClosedImmersionToBOfProperSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    [Fact (flatOver 𝒢 f)] (u : ℱ ⟶ 𝒢)
    [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  isClosedImmersion_toB_of_properSupport f (Fact.out : flatOver 𝒢 f) u

/-- For a finite-type source module, relative flatness, finite presentation, and proper
support of the target make the vanishing locus finitely presented over the base of a
locally finitely presented morphism. -/
instance instFinitePresentationToBOfProperSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    [Fact (flatOver 𝒢 f)] (u : ℱ ⟶ 𝒢)
    [ℱ.IsFiniteType] [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  finitePresentation_toB_of_properSupport f (Fact.out : flatOver 𝒢 f) u

end zeroOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
