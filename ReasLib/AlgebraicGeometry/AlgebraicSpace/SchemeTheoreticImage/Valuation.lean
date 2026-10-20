/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Valuative realization of points of scheme-theoretic images

A point of the scheme-theoretic image of a quasi-compact morphism of algebraic
spaces is realized by a valuation ring whose generic point lifts to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- Every point of the scheme-theoretic image of a quasi-compact morphism of
algebraic spaces over a scheme is the image of the closed point of a valuation-ring
spectrum whose fraction-field spectrum lifts to the source in a commutative square. -/
@[stacks 089B]
theorem exists_valuationRing_diagram {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] (z : Points Z) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (σ : Spec (.of A) ⟶ S)
      (genericToX :
        ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ σ)) ⟶ X)
      (valuationToImage : ofOver (Over.mk σ) ⟶ Z),
      CommSq genericToX (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)
          toImage valuationToImage ∧
        Points.mapOfOver valuationToImage (IsLocalRing.closedPoint A) = z := sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
