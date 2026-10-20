module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.SheafCohomology
import StacksCheckRecall

/-!
# Remark 15.87.8 (Rlim as cohomology)

@stack 091A
-/

@[expose] public section

open CategoryTheory

/-
Remark 15.87.8 (Rlim as cohomology) [091A].  Let `ℕ` carry the bottom (chaotic)
Grothendieck topology.  Its sheaves are sequential inverse systems, and the global-sections
functor is inverse limit.  Consequently the ordinary right-derived inverse-limit functors are
the site cohomology functors `Sheaf.functorH` after transport along
`sheafBotEquivalence AddCommGrpCat`.

The shared library owns the two levels separately: `NaturalNumbersSite.GlobalSections.isoLimit`
is the underived bottom-site bridge, while
`NaturalNumbersSite.Comparison.rightDerived_iso_cohomology` is the
source-facing derived comparison.  The generic theorem
`Sheaf.rightDerivedGlobalSections_isIsomorphic_functorH` is the reusable site-level statement;
the natural-number site is only its specialization.
-/

@[stacks 091A]
#check @CategoryTheory.DerivedLimit.NaturalNumbersSite.GlobalSections.isoLimit

@[stacks 091A]
#check @CategoryTheory.DerivedLimit.NaturalNumbersSite.Comparison.rightDerived_iso_cohomology

#check @CategoryTheory.DerivedLimit.NaturalNumbersSite.Comparison.rightDerived_obj_iso_cohomology

#check @CategoryTheory.Sheaf.globalSectionsExtZeroEquiv
#check @CategoryTheory.Sheaf.globalSectionsNatIsoExtZero
#check @CategoryTheory.Sheaf.rightDerivedGlobalSections_isIsomorphic_functorH

end
