/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Irreducibility

open CategoryTheory Set TopologicalSpace

universe u

/- Lemma 53.9.2: `I(Z)` is represented intrinsically by the standard-chart coordinate ideal;
the resulting generator criterion is the shared projective-plane irreducibility theorem. -/
@[stacks 0BYC] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.curve_iff_irreducible_generator :
    ∀ (k : Type u) [Field k]
      (Z : (AlgebraicGeometry.ProjectiveSpace.scheme k 2).IdealSheafData)
      [Nonempty Z.subscheme]
      (h_componentDim : ∀ C : irreducibleComponents Z.subscheme,
        topologicalKrullDim (C : Set Z.subscheme) = 1)
      (h_noEmbeddedPoints : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
      (F : MvPolynomial (Fin 3) k)
      (h_generator :
        AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.coordinateIdeal 2 Z =
          Ideal.span {F}),
      AlgebraicGeometry.Curve
        (CategoryTheory.Over.mk
          (Z.subschemeι ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k 2)) ↔
        Irreducible F)
