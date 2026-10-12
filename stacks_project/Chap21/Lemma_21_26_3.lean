/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Derived.Sections.MayerVietoris
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.26.3

The reusable owner is
`CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris`.  This chapter file keeps
the Stacks label as a recall surface and does not duplicate the derived-section construction.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open scoped GrothendieckTopologyDerivedSections

/- Lemma 21.26.3 (0EVY): a sheafified-representable pushout with a monomorphic overlap gives a
functorial distinguished Mayer--Vietoris triangle of derived sections. -/
@[stacks 0EVY]
#check @exists_triangle

@[stacks 0EVY]
#check @toBiprod

@[stacks 0EVY]
#check @difference

@[stacks 0EVY]
#check @toBiprod_comp_difference

#check @restriction
#check @restrictionToDerived
#check @restrictionDerived
#check @restrictionDerived_comp

end
