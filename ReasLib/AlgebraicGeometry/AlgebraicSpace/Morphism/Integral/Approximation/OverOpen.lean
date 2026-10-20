/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral.Approximation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage

/-!
# Integral finite approximation over an open subspace

An integral morphism with quasi-compact quasi-separated target admits a directed
inverse system of finite morphisms of finite presentation that preserves a
prescribed quasi-compact open inverse image on which the morphism is already
finite and of finite presentation.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed integral finite approximation whose canonical comparisons of
inverse images of a given open subspace are isomorphisms at every stage. -/
structure IntegralFiniteApproximationOverOpen {S : Scheme.{u}}
    {X Y V : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (ι : V ⟶ Y) [IsOpenImmersion ι] extends IntegralFiniteApproximation f where
  /-- Each canonical comparison of open inverse images is an isomorphism. -/
  stageInverseImageIso :
    ∀ i : toIntegralFiniteApproximation.I,
      IsIso (openInverseImageMap f (toIntegralFiniteApproximation.stageHom i)
        (toIntegralFiniteApproximation.toStage i) ι (by
          exact (Category.assoc _ _ _).trans (toIntegralFiniteApproximation.over_lim i)))

namespace IntegralFiniteApproximationOverOpen

/-- Refine an integral finite approximation by requiring its canonical open
inverse-image comparisons to be isomorphisms. -/
def of {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] (ι : V ⟶ Y) [IsOpenImmersion ι]
    (A : IntegralFiniteApproximation f)
    (stageInverseImageIso : ∀ i : A.I,
      IsIso (openInverseImageMap f (A.stageHom i) (A.toStage i) ι (by
        exact (Category.assoc _ _ _).trans (A.over_lim i)))) :
    IntegralFiniteApproximationOverOpen f ι where
  toIntegralFiniteApproximation := A
  stageInverseImageIso := stageInverseImageIso

/-- The canonical morphism from the open inverse image in the source to the
open inverse image at a stage of an integral finite approximation. -/
def inverseImageMap {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] {ι : V ⟶ Y} [IsOpenImmersion ι]
    (A : IntegralFiniteApproximationOverOpen f ι) (i : A.I) :
    openInverseImage f ι ⟶
      openInverseImage (A.toIntegralFiniteApproximation.stageHom i) ι :=
  openInverseImageMap f (A.toIntegralFiniteApproximation.stageHom i)
    (A.toIntegralFiniteApproximation.toStage i) ι (by
      exact (Category.assoc _ _ _).trans (A.over_lim i))

/-- An integral finite approximation over an open recovers the original
morphism over its target, has finite stages of finite presentation, and has
isomorphic canonical comparisons of open inverse images at every stage. -/
theorem spec {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] {ι : V ⟶ Y} [IsOpenImmersion ι]
    (A : IntegralFiniteApproximationOverOpen f ι) :
    (∀ i : A.I, A.toIntegralFiniteApproximation.toStage i ≫
      A.toIntegralFiniteApproximation.stageHom i = f) ∧
      (∀ i : A.I, IsFinite (A.toIntegralFiniteApproximation.stageHom i)) ∧
      (∀ i : A.I, FinitePresentation (A.toIntegralFiniteApproximation.stageHom i)) ∧
      ∀ i : A.I, IsIso (A.inverseImageMap i) :=
  sorry

end IntegralFiniteApproximationOverOpen

/-- An integral morphism with quasi-compact quasi-separated target admits a
directed inverse limit presentation by finite morphisms of finite presentation
whose canonical comparisons are isomorphisms over any prescribed quasi-compact
open on which the original morphism is finite and of finite presentation. -/
theorem exists_integralFiniteApproximationOverOpen
    {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (ι : V ⟶ Y) [IsOpenImmersion ι] [QuasiCompact ι]
    [IsFinite (openInverseImageTo f ι)]
    [FinitePresentation (openInverseImageTo f ι)] :
    Nonempty (IntegralFiniteApproximationOverOpen f ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
