/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Flat.IndFiniteFree
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.81.4: Lazard's theorem

@stack 058G
-/

/- Theorem 10.81.4 (Lazard's theorem): an `R`-module `M` is flat if and only if it is the
colimit of a directed system of finite free `R`-modules. -/
@[stacks 058G]
#check @CategoryTheory.ModuleCat.flat_iff_ind_finiteFree

#check @CategoryTheory.ModuleCat.finiteFree
#check @CategoryTheory.ObjectProperty.ind
