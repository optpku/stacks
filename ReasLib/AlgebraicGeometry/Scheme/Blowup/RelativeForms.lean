/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalProjectiveBundle
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic

/-!
# Relative differential forms on a blowup

This file records the comparison maps of relative differential forms along a blowup of a smooth
scheme along a smooth closed center, together with the derived restriction comparison from the
blowup to its exceptional divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSite.Hom.DerivedAdjunction
open RingedSpace.moduleDerivedPushforward
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

variable {S X X' : Scheme.{u}}

/-- The structure maps of a blowup over `S` form a commutative square over `𝟙 S`. -/
theorem relativeStructureSquare (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] : CommSq b (b ≫ f) f (𝟙 S) := sorry

/-- The exceptional projection and the structure maps to `S` form a commutative square. -/
theorem exceptionalStructureSquare (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] :
    CommSq (exceptionalProjection I b)
      (exceptionalProjection I b ≫ I.subschemeι ≫ f) (I.subschemeι ≫ f) (𝟙 S) := sorry

/-- The exceptional immersion and the structure maps to `S` form a commutative square. -/
theorem exceptionalInclusionStructureSquare
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    CommSq (I.comap b).subschemeι
      (exceptionalProjection I b ≫ I.subschemeι ≫ f) (b ≫ f) (𝟙 S) := sorry

/-- Derived pushforward along either composite of ringed-space morphisms in the exceptional
square agrees on relative differential forms. -/
theorem exceptionalCompositeDerivedPushforward_eq
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (a : ℕ) :
    (RingedSpace.moduleDerivedPushforward
        ((I.comap b).subschemeι.toShHom ≫ b.toShHom)).obj
      ((DerivedCategory.singleFunctor (I.comap b).subscheme.Modules 0).obj
        (Λ[a] Ω[(exceptionalProjection I b ≫ I.subschemeι ≫ f).toShHom])) =
      (RingedSpace.moduleDerivedPushforward
        ((exceptionalProjection I b).toShHom ≫ I.subschemeι.toShHom)).obj
        ((DerivedCategory.singleFunctor (I.comap b).subscheme.Modules 0).obj
          (Λ[a] Ω[(exceptionalProjection I b ≫ I.subschemeι ≫ f).toShHom])) := by
  have h :
      (I.comap b).subschemeι.toShHom ≫ b.toShHom =
        (exceptionalProjection I b).toShHom ≫ I.subschemeι.toShHom := by
    rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
      ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom]
    simp [exceptionalProjection, Scheme.IdealSheafData.subschemeMap_subschemeι]
  simp [h]

/-- The canonical derived restriction comparison from a blowup to its exceptional divisor. -/
noncomputable def exceptionalRestrictionDerivedComparison
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    [HasPair
      (RingedSpace.opensRingedSiteHom (I.comap b).subschemeι.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom b.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom
        ((I.comap b).subschemeι.toShHom ≫ b.toShHom))]
    [HasPair
      (RingedSpace.opensRingedSiteHom (exceptionalProjection I b).toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom I.subschemeι.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom
        ((exceptionalProjection I b).toShHom ≫ I.subschemeι.toShHom))]
    (a : ℕ) :
    (RingedSpace.moduleDerivedPushforward b.toShHom).obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj
          (Λ[a] Ω[(b ≫ f).toShHom])) ⟶
      (RingedSpace.moduleDerivedPushforward I.subschemeι.toShHom).obj
        ((RingedSpace.moduleDerivedPushforward
          (exceptionalProjection I b).toShHom).obj
          ((DerivedCategory.singleFunctor (I.comap b).subscheme.Modules 0).obj
            (Λ[a] Ω[(exceptionalProjection I b ≫ I.subschemeι ≫ f).toShHom]))) :=
  (RingedSpace.moduleDerivedPushforward b.toShHom).map
      (RingedSpace.moduleDerivedPushforward.comparison
        (I.comap b).subschemeι.toShHom
        (Λ[a] Ω[(b ≫ f).toShHom])
        (Λ[a] Ω[(exceptionalProjection I b ≫ I.subschemeι ≫ f).toShHom])
        (Scheme.RelativeDifferentials.pushforwardComparison
          (exceptionalInclusionStructureSquare f I b) a)) ≫
    (@Composition.iso _ _ _
      (I.comap b).subschemeι.toShHom b.toShHom
      _ _ _ _ _ _ _ _ _ inferInstance inferInstance inferInstance
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (I.comap b).subschemeι.toShHom b.toShHom)).hom.app
        ((DerivedCategory.singleFunctor (I.comap b).subscheme.Modules 0).obj
          (Λ[a] Ω[(exceptionalProjection I b ≫ I.subschemeι ≫ f).toShHom])) ≫
    eqToHom (exceptionalCompositeDerivedPushforward_eq f I b a) ≫
    (@Composition.comparison _ _ _
      (exceptionalProjection I b).toShHom I.subschemeι.toShHom
      _ _ _ _ _ _ _ _ _ inferInstance inferInstance inferInstance
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (exceptionalProjection I b).toShHom I.subschemeι.toShHom)).app
      ((DerivedCategory.singleFunctor (I.comap b).subscheme.Modules 0).obj
        (Λ[a] Ω[(exceptionalProjection I b ≫ I.subschemeι ≫ f).toShHom]))

/-- For every `a : ℕ`, the canonical map from relative `a`-forms on `X` to the direct image of
relative `a`-forms on its blowup is an isomorphism, when `X` and the center are smooth over `S`. -/
instance relativeDifferentialToBlowupPushforward_isIso
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] (a : ℕ) :
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (relativeStructureSquare f I b) a) := sorry

/-- For every `a : ℕ`, the canonical map from relative `a`-forms on the center to the direct
image of relative `a`-forms on the exceptional divisor is an isomorphism, when `X` and the
center are smooth over `S`. -/
instance centerDifferentialToExceptionalPushforward_isIso
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] (a : ℕ) :
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (exceptionalStructureSquare f I b) a) := sorry

/-- In every cohomological degree `q ≥ 1`, the canonical map from the derived direct image of
relative `a`-forms on the blowup to the iterated derived direct image from the exceptional
divisor is an isomorphism on cohomology sheaves, when `X` and the center are smooth over `S`. -/
instance blowupToExceptionalDerivedCohomology_isIso
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I]
    [HasPair
      (RingedSpace.opensRingedSiteHom (I.comap b).subschemeι.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom b.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom
        ((I.comap b).subschemeι.toShHom ≫ b.toShHom))]
    [HasPair
      (RingedSpace.opensRingedSiteHom (exceptionalProjection I b).toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom I.subschemeι.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom
        ((exceptionalProjection I b).toShHom ≫ I.subschemeι.toShHom))]
    (a q : ℕ) [NeZero q] :
    IsIso ((DerivedCategory.homologyFunctor X.Modules (q : ℤ)).map
      (exceptionalRestrictionDerivedComparison f I b a)) := sorry


/-- The canonical derived comparison from relative exterior differential forms on a scheme to
the derived pushforward of relative exterior differential forms on its blowup. -/
noncomputable def relativeDifferentialDerivedComparison
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] (a : ℕ) :
    (DerivedCategory.singleFunctor X.Modules 0).obj (Λ[a] Ω[f.toShHom]) ⟶
      (RingedSpace.moduleDerivedPushforward b.toShHom).obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj (Λ[a] Ω[(b ≫ f).toShHom])) :=
  RingedSpace.moduleDerivedPushforward.comparison b.toShHom
    (Λ[a] Ω[f.toShHom]) (Λ[a] Ω[(b ≫ f).toShHom])
    (Scheme.RelativeDifferentials.pushforwardComparison
      (relativeStructureSquare f I b) a)

/-- The blowup-relative derived comparison is induced by the canonical underived comparison on
relative exterior differential forms. -/
theorem relativeDifferentialDerivedComparison_def
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] (a : ℕ) :
    relativeDifferentialDerivedComparison f I b a =
      RingedSpace.moduleDerivedPushforward.comparison b.toShHom
        (Λ[a] Ω[f.toShHom]) (Λ[a] Ω[(b ≫ f).toShHom])
        (Scheme.RelativeDifferentials.pushforwardComparison
          (relativeStructureSquare f I b) a) := sorry

/-- For a blowup of a smooth scheme along a smooth center and every `a : ℕ`, the canonical derived
comparison on relative `a`-forms has a unique retraction. -/
theorem existsUnique_relativeDifferentialRetraction
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] (a : ℕ) :
    ∃! r :
      (RingedSpace.moduleDerivedPushforward b.toShHom).obj
          ((DerivedCategory.singleFunctor X'.Modules 0).obj
            (Λ[a] Ω[(b ≫ f).toShHom])) ⟶
        (DerivedCategory.singleFunctor X.Modules 0).obj (Λ[a] Ω[f.toShHom]),
      relativeDifferentialDerivedComparison f I b a ≫ r = 𝟙 _ := sorry

end AlgebraicGeometry.IsBlowup
