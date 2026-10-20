/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.Exact
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Signed
import StacksCheckRecall

/-!
# Lemma 14.23.8 compatibility facade

@stack 019B

The source-signed lower-face exact functor is exported by ReasLib.  Mathlib's d₀-oriented exact
functor remains available below as a convention-specific companion.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicTopology.normalizedMooreComplex.lowerFace

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Lemma 14.23.8: the source-signed normalized Moore complex functor is exact. -/
@[stacks 019B]
#check (exactFunctor (A := A) : SimplicialObject A ⥤ₑ ChainComplex A ℕ)

@[stacks 019B "exactness property of the source-signed normalized Moore functor"]
#check ((exactFunctor (A := A)).property :
  CategoryTheory.exactFunctor (SimplicialObject A) (ChainComplex A ℕ)
    (normalizedMooreComplex.lowerFace (A := A)))

/- Mathlib's d₀-oriented exact owner remains available as a convention-specific companion. -/
#check (CategoryTheory.Abelian.DoldKan.N.exactFunctor (A := A) :
  SimplicialObject A ⥤ₑ ChainComplex A ℕ)

end AlgebraicTopology.normalizedMooreComplex.lowerFace
