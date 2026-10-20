/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator.AlmostBlowup
public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Square
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Frobenius-colimit comparison for a two-generator projective spectrum

This module constructs the canonical restriction square on finite locally free modules over
Frobenius-colimit structure sheaves for the two-generator almost blowup square.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwoGeneratorProj

/-- The canonical almost blowup square determined by two elements of a commutative ring. -/
def almostBlowupSquare (A : CommRingCat.{u}) (f₁ f₂ : A) : Square Scheme.{u} :=
  (toSpec_isAlmostBlowupSquare A f₁ f₂).square

namespace FrobeniusColimit

/-- The base vertex of the canonical two-generator almost blowup square has the characteristic
of the coefficient ring. -/
instance almostBlowupSquareX4IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f₁ f₂ : A) :
    Scheme.IsCharP (almostBlowupSquare A f₁ f₂).X₄ p := sorry

/-- The projective vertex of the canonical two-generator almost blowup square inherits the
characteristic of the base. -/
instance almostBlowupSquareX2IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f₁ f₂ : A) :
    Scheme.IsCharP (almostBlowupSquare A f₁ f₂).X₂ p := sorry

/-- The center vertex of the canonical two-generator almost blowup square inherits the
characteristic of the base. -/
instance almostBlowupSquareX3IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f₁ f₂ : A) :
    Scheme.IsCharP (almostBlowupSquare A f₁ f₂).X₃ p := sorry

/-- The exceptional vertex of the canonical two-generator almost blowup square inherits the
characteristic of the projective vertex. -/
instance almostBlowupSquareX1IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f₁ f₂ : A) :
    Scheme.IsCharP (almostBlowupSquare A f₁ f₂).X₁ p := sorry

open AlgebraicGeometry.Scheme.FrobeniusColimit

/-- The canonical restriction square on finite locally free modules over Frobenius-colimit
structure sheaves for the two-generator almost blowup square. -/
def restrictionSquare (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f₁ f₂ : A) :
    let sq := almostBlowupSquare A f₁ f₂
    CategoricalPullback.CatCommSqOver
      (ModuleModel.pullback p sq.f₁₃) (ModuleModel.pullback p sq.f₁₂)
      (finiteLocallyFreeModules p sq.X₄) :=
  let sq := almostBlowupSquare A f₁ f₂
  { fst := ModuleModel.pullback p sq.f₃₄
    snd := ModuleModel.pullback p sq.f₂₄
    iso := (ModuleModel.pullbackCompIso p sq.f₁₃ sq.f₃₄).symm ≪≫
      eqToIso (congrArg (fun h : sq.X₁ ⟶ sq.X₄ ↦ ModuleModel.pullback p h) sq.fac.symm) ≪≫
      ModuleModel.pullbackCompIso p sq.f₁₂ sq.f₂₄ }

/-- The first projection of the canonical restriction square is pullback from the base to the
center. -/
theorem restrictionSquare_fst (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f₁ f₂ : A) :
    (restrictionSquare p A f₁ f₂).fst =
      ModuleModel.pullback p (almostBlowupSquare A f₁ f₂).f₃₄ := sorry

/-- The second projection of the canonical restriction square is pullback from the base to the
projective vertex. -/
theorem restrictionSquare_snd (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f₁ f₂ : A) :
    (restrictionSquare p A f₁ f₂).snd =
      ModuleModel.pullback p (almostBlowupSquare A f₁ f₂).f₂₄ := sorry

/-- The structural isomorphism of the canonical restriction square is induced by the square
equation and functoriality of pullback. -/
theorem restrictionSquare_iso (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f₁ f₂ : A) :
    let sq := almostBlowupSquare A f₁ f₂
    (restrictionSquare p A f₁ f₂).iso =
      (ModuleModel.pullbackCompIso p sq.f₁₃ sq.f₃₄).symm ≪≫
        eqToIso
          (congrArg (fun h : sq.X₁ ⟶ sq.X₄ ↦ ModuleModel.pullback p h) sq.fac.symm) ≪≫
        ModuleModel.pullbackCompIso p sq.f₁₂ sq.f₂₄ := sorry

/-- The canonical comparison from the Frobenius-colimit module model on the base to the
categorical pullback of the models on the center and projective vertices over the exceptional
vertex. -/
def comparison (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f₁ f₂ : A) :=
  (restrictionSquare p A f₁ f₂).comparison

/-- The canonical restriction comparison for the two-generator almost blowup square is an
equivalence. -/
instance comparisonIsEquivalence (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f₁ f₂ : A) :
    (comparison p A f₁ f₂).IsEquivalence := sorry

end FrobeniusColimit

end AlgebraicGeometry.TwoGeneratorProj
