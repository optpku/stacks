module

public import ReasLib.CategoryTheory.Abelian.Projective.Dimension.Ext
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.109.8

@stack 065R

The reusable owner proves the source TFAE in every abelian category with Ext
and enough injectives; the module-category statement is a direct
specialization.
-/

@[stacks 065R "projective dimension and Ext vanishing"]
#check @CategoryTheory.HasProjectiveDimensionLE.ext_vanishing_tfae

#check @CategoryTheory.HasProjectiveDimensionLE.iff_ext_eq_zero_of_ge
#check @CategoryTheory.HasProjectiveDimensionLE.iff_ext_eq_zero_at_succ
