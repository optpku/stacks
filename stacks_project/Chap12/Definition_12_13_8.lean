/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Homotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex ComplexShape

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable (K L : CochainComplex V ℤ) (f : K ⟶ L)

/- Definition 12.13.8 [0113]: homotopy equivalence of cochain complexes is the canonical
homological-complex morphism property. -/
@[stacks 0113]
#check (HomologicalComplex.homotopyEquivalences V (up ℤ) f : Prop)

#check (HomotopyEquiv K L : Type _)
