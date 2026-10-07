module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Equivalence
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 15.91.16 (0BP2)

@stack 0BP2
-/

-- Theorem 15.91.16, the full-subcategory property of glueable modules.
@[stacks 0BP2 "Theorem 15.91.16, glueable modules"]
#check @LocalizedModule.Away.FormalGluing.Single.glueableProperty

-- Theorem 15.91.16, canonical formal gluing restricted to glueable modules.
@[stacks 0BP2 "Theorem 15.91.16, restricted functor"]
#check @LocalizedModule.Away.FormalGluing.Single.glueableFunctor

-- Theorem 15.91.16, the Beauville-Laszlo equivalence for a gluing pair.
@[stacks 0BP2 "Theorem 15.91.16, equivalence"]
#check @LocalizedModule.Away.FormalGluing.Single.glueableFunctor_isEquivalence
