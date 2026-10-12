/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.LowerFace
import StacksCheckRecall

/-!
@stack 017V

# Lemma 14.18.6 compatibility facade

The lower-face splitting is owned in ReasLib at the natural level of simplicial objects in an
arbitrary abelian category.  This module retains the historical Chapter 14 import path.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U : SimplicialObject A) (n : ℕ) (Δ : SimplexCategoryᵒᵖ)

/- Lemma 14.18.6 (1): in degree zero the lower-face normalized summand is the whole object. -/
@[stacks 017V "Lemma 14.18.6 (1)"]
#check (normalizedMoore.lowerFace.subobject.zero U :
  normalizedMoore.lowerFace.subobject U 0 = ⊤)

/- Lemma 14.18.6 (2): in positive degree the summand is the intersection of the lower-face
kernels. -/
@[stacks 017V "Lemma 14.18.6 (2)"]
#check (normalizedMoore.lowerFace.subobject.add_one U n :
  normalizedMoore.lowerFace.subobject U (n + 1) =
    Finset.univ.inf (fun k : Fin (n + 1) ↦
      kernelSubobject (U.δ (Fin.castSucc k))))

/- Lemma 14.18.6 (3): these summands give the canonical coproduct decomposition in every
simplicial degree. -/
@[stacks 017V "Lemma 14.18.6 (3)"]
#check (inferInstance : IsIso (normalizedMoore.lowerFace.decomposition U Δ))

/- Lemma 14.18.6 (4): the lower-face splitting is functorial in the simplicial object. -/
@[stacks 017V "Lemma 14.18.6 (4)"]
#check (normalizedMoore.lowerFace.splitting.functor (A := A) :
  SimplicialObject A ⥤ Split A)

end CategoryTheory.SimplicialObject
