module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Restriction
import StacksCheckRecall

/-!
# Lemma 15.75.8

@stack 066V

If `B` is perfect as an `A`-module and `K` is perfect over `B`, then restriction of scalars makes
`K` perfect over `A`.  The reusable owner is stated for an explicit ring homomorphism and its
canonical target module `f.targetModule`.
-/

@[expose] public section

open CategoryTheory

@[stacks 066V "Lemma 15.75.8"]
#check @DerivedCategory.IsPerfect.restrictScalars
