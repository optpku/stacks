/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import ReasLib.CategoryTheory.MorphismProperty.SiteLocal
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

variable (S : AlgebraicGeometry.Scheme.{u})

/- Definition 74.14.1: for a scheme `S`, a property `P` of morphisms of algebraic
spaces over `S`, and a precoverage `K` equal to one of the fpqc, fppf, syntomic,
smooth, or étale precoverages on `AlgebraicSpace S`, we say `P` is τ-local on the
source, or local on the source for the τ-topology, if for every morphism
`f : X ⟶ Y` of algebraic spaces over `S` and every `K`-cover `𝒰` of `X`,
`P f ↔ ∀ i, P (𝒰.f i ≫ f)`. -/
@[stacks 06EP] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.iff_forall_zeroHypercover :
    ∀ (P : CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
      (K : CategoryTheory.Precoverage (AlgebraicGeometry.AlgebraicSpace S))
      [P.RespectsIso],
      P.IsLocalAtSource K ↔
        ∀ ⦃X Y : AlgebraicGeometry.AlgebraicSpace S⦄ (f : X ⟶ Y)
          (𝒰 : CategoryTheory.Precoverage.ZeroHypercover K X),
          P f ↔ ∀ i, P (𝒰.f i ≫ f))
