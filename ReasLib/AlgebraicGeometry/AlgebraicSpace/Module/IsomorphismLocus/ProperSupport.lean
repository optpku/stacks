/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismOverSFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Isomorphism loci of modules with proper support

For a surjective morphism of quasi-coherent modules, local finite presentation and
relative flatness of the source module with proper support give an algebraic
isomorphism locus whose structural morphism is a closed immersion. If the target
module is of finite presentation, this morphism is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

namespace isomorphismOverSFunctor

/-- For a locally finitely presented morphism `f` and a surjective module morphism,
if the source module is locally of finite presentation, flat over `B`, and has
support proper over `B`, then its isomorphism functor is an algebraic space. -/
theorem isAlgebraicSpace_of_properSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (u : ℱ ⟶ 𝒢) [Epi u] :
    IsAlgebraicSpace (isomorphismOverSFunctor f u) :=
  sorry

/-- For a locally finitely presented morphism `f` and a surjective module morphism,
if the source module is locally of finite presentation, flat over `B`, and has
support proper over `B`, then the isomorphism space maps to `B` by a closed immersion. -/
theorem isClosedImmersion_toB_of_properSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (u : ℱ ⟶ 𝒢) [Epi u]
    [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  sorry

/-- For a locally finitely presented morphism `f` and a surjective module morphism,
if the source module is locally of finite presentation, flat over `B`, and has
support proper over `B`, and the target module is of finite presentation, then the
isomorphism space is of finite presentation over `B`. -/
theorem finitePresentation_toB_of_properSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (u : ℱ ⟶ 𝒢) [Epi u]
    [𝒢.IsFinitePresentation] [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  sorry

/-- Relative flatness and proper support of a locally finitely presented source
module make the isomorphism functor of a surjection an algebraic space when `f`
is locally of finite presentation. -/
instance instIsAlgebraicSpaceOfProperSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    [h_flat : Fact (flatOver ℱ f)] (u : ℱ ⟶ 𝒢) [Epi u] :
    IsAlgebraicSpace (isomorphismOverSFunctor f u) :=
  isAlgebraicSpace_of_properSupport f h_flat.out u

/-- Relative flatness and proper support of a locally finitely presented source
module make the structural morphism of the isomorphism space of a surjection a
closed immersion when `f` is locally of finite presentation. -/
instance instIsClosedImmersionToBOfProperSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    [h_flat : Fact (flatOver ℱ f)] (u : ℱ ⟶ 𝒢) [Epi u]
    [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  isClosedImmersion_toB_of_properSupport f h_flat.out u

/-- For a surjection from a locally finitely presented module to a finitely
presented module, relative flatness and proper support of the source module make
the isomorphism space of finite presentation over `B` when `f` is locally of finite
presentation. -/
instance instFinitePresentationToBOfProperSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    [h_flat : Fact (flatOver ℱ f)] (u : ℱ ⟶ 𝒢) [Epi u]
    [𝒢.IsFinitePresentation] [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  finitePresentation_toB_of_properSupport f h_flat.out u

end isomorphismOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
