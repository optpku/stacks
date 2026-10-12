/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.DegreeTwo
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.23.2: let `k` be an algebraically closed field, let `X` be a proper `k`-scheme, and
let `L` be an invertible `𝒪_X`-module. If sections restrict surjectively to every zero-dimensional
closed subscheme of degree two, then `L` is very ample on `X` over `k`. -/
@[stacks 0E8T] #check
  (AlgebraicGeometry.relativelyVeryAmple_of_degreeTwo_restriction_surjective :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (L : X.Modules) [Scheme.Modules.Invertible L],
      (∀ Z : X.IdealSheafData,
        topologicalKrullDim Z.subscheme = 0 →
          Module.finrank k (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ f)) = 2 →
            Function.Surjective (Scheme.Modules.sectionsPullback Z.subschemeι L)) →
        RelativelyVeryAmple f L)
