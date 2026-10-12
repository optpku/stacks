/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
import StacksCheckRecall

/-!
# Lemma 15.92.6: derived-complete objects

@stack 091U

The weak-Serre instance and the cohomology-in comparison are shared infrastructure.  This chapter
file is deliberately a tagged recall surface; downstream files should import the ReasLib owner
directly when they need the APIs.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.92.6 (Stacks `091U`) (1): derived-complete modules form a weak Serre subcategory. -/
@[stacks 091U "derived-complete modules form a weak Serre subcategory"]
#check @ModuleCat.DerivedComplete.isWeakSerreClass

/- Lemma 15.92.6 (Stacks `091U`) (2): the derived-complete derived objects are the full
subcategory whose cohomology modules are derived complete. -/
@[stacks 091U "derived-complete objects are detected on cohomology"]
#check @DerivedCategory.DerivedComplete.property_eq_cohomologyIn

@[stacks 091U "derived-complete cohomology-in membership"]
#check @DerivedCategory.DerivedComplete.mem_iff

end
