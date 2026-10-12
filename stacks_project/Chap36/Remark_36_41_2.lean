/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.AffineOver.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Remark 36.41.2: for every scheme `S`, quasi-coherent derived modules on the chaotic
category of all affine schemes over `S` are canonically equivalent to derived `𝒪_S`-modules
with quasi-coherent cohomology. -/
@[stacks 0H00] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.AffineOverQC.comparisonIsEquivalence :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.DerivedQCoh.AffineOverQC.comparison S))
