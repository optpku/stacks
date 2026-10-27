/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Colimits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-! # Exactness and extension closure of quasi-coherent modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- The inclusion of quasi-coherent modules into modules on the big fppf site
 of the affine scheme over the integers is not exact. -/
theorem inclusion_not_exact :
    ¬ exactFunctor
        (QCoh (GroupoidsOver.slice (Over.mk (𝟙 (Spec (CommRingCat.of ℤ))))))
        (RingedSite.ModuleCat (ringedSite _)) (inclusion _) := sorry

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The inclusion of quasi-coherent modules preserves finite colimits. -/
instance inclusion_preservesFiniteColimits [AlgebraicStack X] :
    PreservesFiniteColimits (inclusion X) := sorry

/-- The inclusion of quasi-coherent modules into fppf modules is right exact. -/
theorem inclusion_rightExact [AlgebraicStack X] :
    rightExactFunctor (QCoh X) (RingedSite.ModuleCat.{u} (ringedSite X))
      (inclusion X) := inclusion_preservesFiniteColimits

/-- The inclusion of quasi-coherent modules preserves colimits of every
 universe-compatible shape because it creates them. -/
instance inclusion_preservesColimitsOfShape [AlgebraicStack X]
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (inclusion X) :=
  preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape (inclusion X)

/-- Quasi-coherent modules on an algebraic stack are closed under extensions
 in the ambient fppf module category. -/
instance closedUnderExtensions [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := sorry

/-- In a short exact sequence of fppf modules with quasi-coherent outer terms,
 the middle term is quasi-coherent. -/
theorem isQuasicoherent_of_shortExact [AlgebraicStack X]
    {sc : ShortComplex (RingedSite.ModuleCat.{u} (ringedSite X))}
    (hsc : sc.ShortExact)
    (h₁ : quasiCoherentModuleProperty X sc.X₁)
    (h₃ : quasiCoherentModuleProperty X sc.X₃) :
    quasiCoherentModuleProperty X sc.X₂ :=
  (quasiCoherentModuleProperty X).prop_X₂_of_shortExact hsc h₁ h₃

end AlgebraicGeometry.GroupoidsOver.QCoh
