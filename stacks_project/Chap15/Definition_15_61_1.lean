module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence

/-!
# Tor independence

@stack 0660
-/

@[expose] public section

open CategoryTheory

universe u

section

variable (R : Type u) [CommRing R]
variable (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/- Definition 15.61.1: two `R`-algebras are Tor independent when their underlying bundled
`R`-modules satisfy the canonical Tor-independence predicate. -/
@[stacks 0660 "Definition 15.61.1: bundled modules"]
#check (CategoryTheory.ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B) : Prop)

#check @CategoryTheory.ModuleCat.Tor.obj
#check @CategoryTheory.ModuleCat.Tor.IsIndependent
#check @CategoryTheory.ModuleCat.Tor.IsIndependent.isZero
#check @CategoryTheory.ModuleCat.Tor.IsIndependent.iff_succ

end
