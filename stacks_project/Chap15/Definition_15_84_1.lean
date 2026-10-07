module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
import Mathlib.RingTheory.FinitePresentation
import StacksCheckRecall

/-!
# Definition 15.84.1

@stack 0DHS
-/

@[expose] public section

open CategoryTheory

universe u

/- Definition 15.84.1 (Stacks `0DHS`): under the source setup that `R → A` is flat and of finite
presentation, an object `K : D(A)` is `R`-perfect when it is pseudo-coherent over `A` and has
finite Tor dimension over `R`.  The reusable owner is intentionally defined for every
commutative algebra; the flat finite-presentation assumptions belong to the later theorems. -/
@[stacks 0DHS]
#check fun (R : Type u) (A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) =>
  (CategoryTheory.DerivedCategory.IsPerfectOver R K : Prop)

end
