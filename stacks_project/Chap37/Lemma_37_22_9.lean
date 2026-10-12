/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Flat

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Lemma 37.22.9: a flat, locally finitely presented morphism admits open pieces of
each relative dimension whose union is dense in every fibre. -/
@[stacks 054T]
#check (AlgebraicGeometry.Scheme.Hom.exists_open_relativeDimension_decomposition :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
    ∃ U : ℕ → X.Opens,
      (∀ s : S, Dense ((f.fiberι s) ⁻¹' (iSup U : X.Opens))) ∧
        ∀ d : ℕ, AlgebraicGeometry.Scheme.Hom.RelativeDimension ((U d).ι ≫ f) d)
