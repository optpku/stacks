/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismOverSFunctor

/-!
# Algebraic-space structure on the isomorphism functor

Under finite presentation of the morphism and of `ℱ`, together with relative flatness
and purity of `ℱ` and surjectivity of `u`, the `(Sch/S)` functor `F_iso` is an algebraic
space, and the structure map `F_iso ⟶ B` is a closed immersion. If `𝒢` is of finite
presentation, that closed immersion is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

namespace isomorphismOverSFunctor

/-- If `f` and `ℱ` are of finite presentation, `ℱ` is flat over `B` and pure relative
to `B`, and `u` is surjective, then the `(Sch/S)` isomorphism functor is an algebraic
space. -/
theorem isAlgebraicSpace [FinitePresentation f] [ℱ.IsFinitePresentation]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (h_pure : ℱ.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [Epi u] :
    IsAlgebraicSpace (isomorphismOverSFunctor f u) :=
  sorry

/-- If `f` and `ℱ` are of finite presentation, `ℱ` is flat over `B` and pure relative
to `B`, and `u` is surjective, then the structure morphism `F_iso ⟶ B` is a closed
immersion. -/
theorem isClosedImmersion_toB [FinitePresentation f] [ℱ.IsFinitePresentation]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (h_pure : ℱ.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [Epi u] [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  sorry

/-- If `f`, `ℱ`, and `𝒢` are of finite presentation, `ℱ` is flat over `B` and pure
relative to `B`, and `u` is surjective, then the structure morphism of the
isomorphism space to `B` is of finite presentation. -/
theorem finitePresentation_toB [FinitePresentation f] [ℱ.IsFinitePresentation]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (h_pure : ℱ.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [Epi u] [𝒢.IsFinitePresentation]
    [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  sorry

end isomorphismOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
