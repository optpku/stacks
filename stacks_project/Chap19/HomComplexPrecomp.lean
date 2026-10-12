/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Precomposition
import StacksCheckRecall

/-!
# Chapter 19 compatibility facade

The general Hom-complex precomposition API is owned by
`ReasLib.Algebra.Homology.CochainComplex.HomComplex.Precomposition`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {L M I : CochainComplex C ℤ}

@[stacks 079L] #check
  fun (f : L ⟶ M) ↦
    (homComplexPrecomp (I := I) f : M.HomComplex I ⟶ L.HomComplex I)

#check @CategoryTheory.CochainComplex.homComplexPrecomp_f
#check @CategoryTheory.CochainComplex.homComplexPrecomp_comp

end CategoryTheory.CochainComplex
