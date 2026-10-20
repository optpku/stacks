/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.MayerVietoris
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FppfComparison
public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Square
public import ReasLib.AlgebraicGeometry.Scheme.Spec.AlmostBlowup
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator.AlmostBlowup
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

open CategoryTheory hiding Square
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.H

/-- The underlying scheme square associated to a square in `Over S`. -/
def toSchemeSquare {S : Scheme.{u}} (sq : Square (Over S)) :
    CategoryTheory.Square Scheme.{u} where
  X₁ := sq.E.left
  X₂ := sq.Y.left
  X₃ := sq.Z.left
  X₄ := sq.X.left
  f₁₂ := sq.toY.left
  f₁₃ := sq.toZ.left
  f₂₄ := sq.inY.left
  f₃₄ := sq.inZ.left
  fac := congrArg (fun f : sq.E ⟶ sq.X ↦ f.left) sq.comm

/-- The upper-right morphism of `toSchemeSquare sq` is the underlying morphism of `sq.inY`. -/
theorem toSchemeSquare_f₂₄ {S : Scheme.{u}} (sq : Square (Over S)) :
    (toSchemeSquare sq).f₂₄ = sq.inY.left := sorry

/-- A square over `S` belongs to one of the two canonical almost-blowup square families. -/
def IsExampleAlmostBlowupSquare {S : Scheme.{u}} (sq : Square (Over S)) : Prop :=
  (∃ (A : CommRingCat.{u}) (f : A) (J : Ideal A) (hJfg : J.FG)
      (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0),
    Nonempty
      (toSchemeSquare sq ≅
        (Spec.quotientMap_isAlmostBlowupSquare A f J hJfg hJ).square)) ∨
    ∃ (A : CommRingCat.{u}) (f₁ f₂ : A),
      Nonempty
        (toSchemeSquare sq ≅
          (TwoGeneratorProj.toSpec_isAlmostBlowupSquare A f₁ f₂).square)

/-- For bounded-below objects, essential-image membership is characterized by the
Mayer–Vietoris condition on every canonical almost-blowup square. -/
theorem essImage_iff_exampleAlmostBlowupCondition
    {S : Scheme.{u}}
    (hle : Scheme.fppfTopology.over S ≤
      (Scheme.hPrecoverage.toGrothendieck).over S)
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1}
      (SiteAbelianSheafCat (Scheme.fppfTopology.over S))]
    [HasWeakSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      (Type (u + 1))]
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (Absolute.pushforward hle))
      (Absolute.qis ((Scheme.hPrecoverage.toGrothendieck).over S))]
    (K : DerivedCategory.Plus (SiteAbelianSheafCat (Scheme.fppfTopology.over S))) :
    Functor.essImage
        (Absolute.rightDerived hle)
        (DerivedCategory.Plus.ι.obj K) ↔
      ∀ (sq : Square (Over S)),
        IsExampleAlmostBlowupSquare sq →
        sq.Condition (Scheme.fppfTopology.over S) (DerivedCategory.Plus.ι.obj K) := sorry

/-- A square over `S` is an affine almost blowup square when its target is affine,
its center map is a closed immersion, its underlying scheme square is cartesian,
and its upper-right map is an almost blowup for the kernel ideal of the center map. -/
def IsAffineAlmostBlowupSquare {S : Scheme.{u}} (sq : Square (Over S)) : Prop :=
  IsAffine sq.X.left ∧
    IsClosedImmersion sq.inZ.left ∧
    IsPullback sq.toY.left sq.toZ.left sq.inY.left sq.inZ.left ∧
    IsAlmostBlowupSquare sq.inY.left (Scheme.Hom.ker sq.inZ.left)

/-- A bounded-below derived object on the big fppf site lies in the essential image
of the unbounded h-to-fppf right-derived direct image if and only if every affine
almost blowup square satisfies its derived Mayer–Vietoris condition. -/
theorem essImage_iff_affineAlmostBlowupCondition {S : Scheme.{u}}
    (K : DerivedCategory.Plus (SiteAbelianSheafCat (Scheme.fppfTopology.over S))) :
    Functor.essImage (Absolute.rightDerived (AlgebraicGeometry.Scheme.H.fppf_le S))
        (DerivedCategory.Plus.ι.obj K) ↔
      ∀ (sq : Square (Over S)),
        IsAffineAlmostBlowupSquare sq →
        sq.Condition (Scheme.fppfTopology.over S) (DerivedCategory.Plus.ι.obj K) := sorry

end AlgebraicGeometry.Scheme.H

end
