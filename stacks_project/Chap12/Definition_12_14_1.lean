/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.ChainShift
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Definition 12.14.1: chain complexes indexed by `ℤ` carry the shift for which
`(K⟦k⟧).X n = K.X (n + k)`, with the usual sign on differentials. -/
@[stacks 011A]
#check (inferInstance : HasShift (ChainComplex C ℤ) ℤ)

/- The canonical degree, differential, and map formulas are exposed separately for downstream
rewriting. -/
#check ChainComplex.shiftFunctor_obj_X
#check ChainComplex.shiftFunctor_obj_d
#check ChainComplex.shiftFunctor_map_f
