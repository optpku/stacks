/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.ZeroFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Algebraic-space structure on the vanishing functor

Under finite presentation of the morphism and of `𝒢`, together with relative flatness
and purity of `𝒢`, the `(Sch/S)` functor `F_zero` is an algebraic space, and the
structure map `F_zero ⟶ B` is a closed immersion. If `ℱ` is of finite type, that
closed immersion is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

namespace zeroOverSFunctor

/-- If `f` and `𝒢` are of finite presentation and `𝒢` is flat over `B` and pure relative
to `B`, then the `(Sch/S)` vanishing functor is an algebraic space. -/
theorem isAlgebraicSpace [FinitePresentation f] [𝒢.IsFinitePresentation]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (hG_pure : 𝒢.IsPureOver f)
    (u : ℱ ⟶ 𝒢) :
    IsAlgebraicSpace (zeroOverSFunctor f u) :=
  sorry

/-- If `f` and `𝒢` are of finite presentation and `𝒢` is flat over `B` and pure relative
to `B`, then the structure morphism `F_zero ⟶ B` is a closed immersion. -/
theorem isClosedImmersion_toB [FinitePresentation f] [𝒢.IsFinitePresentation]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (hG_pure : 𝒢.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  sorry

/-- If `f` and `𝒢` are of finite presentation, `𝒢` is flat over `B` and pure relative
to `B`, and `ℱ` is of finite type, then the structure morphism `F_zero ⟶ B` is of
finite presentation. -/
theorem finitePresentation_toB [FinitePresentation f] [𝒢.IsFinitePresentation]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (hG_pure : 𝒢.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  sorry

end zeroOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
