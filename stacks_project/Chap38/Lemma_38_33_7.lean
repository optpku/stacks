/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.OpenCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/- Lemma 38.33.7: a separated finite-type scheme over a Noetherian base is compactifiable
if it is covered by two compactifiable opens whose intersection is dense. -/
@[stacks 0F40] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.nonempty_of_sup_eq_top_of_dense :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (U : Over S)
      [Scheme.Hom.FiniteType U.hom] [IsSeparated U.hom]
      (U₁ U₂ : U.left.Opens) (_ : U₁ ⊔ U₂ = ⊤)
      (_ : Dense (U₁ ⊓ U₂ : Set U.left))
      [Nonempty (Of S (Over.mk (U₁.ι ≫ U.hom)))]
      [Nonempty (Of S (Over.mk (U₂.ι ≫ U.hom)))],
      Nonempty (Of S U))

end AlgebraicGeometry.Scheme.Compactification
