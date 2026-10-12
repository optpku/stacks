/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RelativeForms
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSite.Hom.DerivedAdjunction
open scoped AlgebraicGeometry

universe u

/- Lemma 50.17.1: with notation as in More on Morphisms, Lemma 37.17.3, for a ≥ 0 the map
Ω^a_{X/S} → b_* Ω^a_{X'/S} is an isomorphism, the map Ω^a_{Z/S} → p_* Ω^a_{E/S} is an
isomorphism, and Rb_* Ω^a_{X'/S} → i_* Rp_* Ω^a_{E/S} is an isomorphism on cohomology sheaves
in degree ≥ 1. -/
@[stacks 0FUU]
#check (AlgebraicGeometry.IsBlowup.relativeDifferentialToBlowupPushforward_isIso :
  ∀ {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] (a : ℕ),
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (AlgebraicGeometry.IsBlowup.relativeStructureSquare f I b) a))

#check (AlgebraicGeometry.IsBlowup.centerDifferentialToExceptionalPushforward_isIso :
  ∀ {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] (a : ℕ),
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (AlgebraicGeometry.IsBlowup.exceptionalStructureSquare f I b) a))

#check (AlgebraicGeometry.IsBlowup.blowupToExceptionalDerivedCohomology_isIso :
  ∀ {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I]
    [HasPair
      (RingedSpace.opensRingedSiteHom (I.comap b).subschemeι.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom b.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom
        ((I.comap b).subschemeι.toShHom ≫ b.toShHom))]
    [HasPair
      (RingedSpace.opensRingedSiteHom
        (AlgebraicGeometry.IsBlowup.exceptionalProjection I b).toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom I.subschemeι.toShHom)]
    [HasPair
      (RingedSpace.opensRingedSiteHom
        ((AlgebraicGeometry.IsBlowup.exceptionalProjection I b).toShHom ≫
          I.subschemeι.toShHom))]
    (a q : ℕ) [NeZero q],
    IsIso ((DerivedCategory.homologyFunctor X.Modules (q : ℤ)).map
      (AlgebraicGeometry.IsBlowup.exceptionalRestrictionDerivedComparison f I b a)))
