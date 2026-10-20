module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction
import StacksCheckRecall

/-!
# Lemma 15.5.4

@stack 0D2F

For a commutative square of rings, the canonical module base-change functor has the explicit
fibre-product right adjoint `CategoryTheory.ModuleCat.Pullback.rightAdjoint`.  The adjunction is
owned by `CategoryTheory.ModuleCat.Pullback.adjunction`.
-/

@[stacks 0D2F "canonical fibre-product right adjoint"]
#check @CategoryTheory.ModuleCat.Pullback.rightAdjoint

@[stacks 0D2F "Lemma 15.5.4 module base-change adjunction"]
#check @CategoryTheory.ModuleCat.Pullback.adjunction
