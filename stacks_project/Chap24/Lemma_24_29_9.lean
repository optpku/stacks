module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Hypercohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.29.9

The generic shifted-representable composition is owned by
`CategoryTheory.Functor.ShiftRepresented`.  Its DG-module specialization, with the regular module
as representing object, is owned by the neutral derived hypercohomology leaf.
-/

open CategoryTheory
open SheafOfModules.RingedSite.DifferentialGradedModule

/- Lemma 24.29.9 (tag 0FTX): the degree-`n` hypercohomology functor is identified with the
   shifted representable functor, and evaluation gives the corresponding morphism-group iso.  The
   recall uses the canonical `preadditiveCoyoneda` object rather than spelling out its carrier. -/
#check @CategoryTheory.Functor.ShiftRepresented.iso
#check @CategoryTheory.Functor.ShiftRepresented.objIso
#check @CategoryTheory.Functor.ShiftRepresented.hom_app
#check @CategoryTheory.Functor.ShiftRepresented.inv_app
@[stacks 0FTX] #check @Hypercohomology.functorIso
#check @Hypercohomology.objIso
#check @Hypercohomology.functorIso_hom_app
#check @Hypercohomology.functorIso_inv_app
