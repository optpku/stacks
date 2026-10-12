/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_20_1_ProjectionFormula
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 75.20.1: for a quasi-compact and quasi-separated morphism of algebraic spaces
over a scheme `S`, the canonical map `Rf_* E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^* K)` is an
isomorphism when `E` and `K` have quasi-coherent cohomology. -/
@[stacks 08IN] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isIso_projectionFormula :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      (E : DerivedQCoh X) (K : DerivedQCoh Y),
      IsIso (leftMate f E.obj K.obj))
