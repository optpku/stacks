/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.Etale

/-!
# Formal smoothness along étale vertical arrows

In a commutative square of algebraic spaces, étale vertical arrows transport
formal smoothness from the bottom morphism to the top morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.19.5: Let `S` be a scheme. In a commutative square of morphisms of
algebraic spaces over `S`, if the vertical arrows are étale and the bottom
arrow `f` is formally smooth, then the top arrow `ψ` is formally smooth. -/
@[stacks 061H] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.of_etale_commSq :
    ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
      {ψ : U ⟶ V} {a : U ⟶ X} {b : V ⟶ Y} {f : X ⟶ Y}
      [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b] [FormallySmooth f],
      CommSq ψ a b f → FormallySmooth ψ)
