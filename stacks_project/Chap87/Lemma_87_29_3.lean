/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalSpectrum.FiniteTypeSystem

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

/- Lemma 87.29.3. For a McQuillan affine formal algebraic space with associated
weakly admissible ring A, finite-type inverse systems of quotient algebras are
anti-equivalent to finite-type maps of affine formal algebraic spaces into it. -/
@[stacks 0AL1] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.instIsEquivalence_spfFiniteTypeSystemOver :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
      {X : (Over S)ᵒᵖ ⥤ Type u} (eX : (spf A hA).obj ≅ X),
      (spfFiniteTypeSystemOver hA eX).IsEquivalence)
