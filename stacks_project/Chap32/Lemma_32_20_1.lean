/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

/- Lemma 32.20.1: let `S` be a scheme and `s` a closed point whose open complement `U` is
quasi-compact. Finite-presentation schemes over `S` are equivalent to compatible
finite-presentation schemes over `U` and over `Spec(𝒪_{S,s})`, identified over the punctured local
scheme. -/
@[stacks 0BPA] #check
  (AlgebraicGeometry.finitePresentationOver_equivalence_stalkGluing :
    ∀ (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
      (s : S) (_ : s ∈ closedPoints S)
      (_ : (U : Set S) = ({s} : Set S)ᶜ),
      Nonempty
        (AlgebraicGeometry.FinitePresentationOver S ≌
          AlgebraicGeometry.finitePresentationStalkGluingCategory S U s))
