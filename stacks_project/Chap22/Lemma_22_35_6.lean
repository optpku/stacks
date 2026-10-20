module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.FullyFaithful
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TensorWithObject
open scoped DifferentialGradedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (K : Complex (J := J) (O := O))
variable (h_compact : IsCompactObject (DerivedCategory.Q.obj K))
variable (h_ext : CategoryTheory.CochainComplex.Enriched.ComputesSelfExt K)

/- Lemma 22.35.6 (09LZ): if `K` is compact and its endomorphism Hom complex computes all
shifted self-Ext groups, then derived tensoring with `K` is fully faithful. -/
@[stacks 09LZ] #check
  (Derived.fullyFaithful K h_compact h_ext :
    (Derived.tensorFunctor K).FullyFaithful)

#check @CategoryTheory.CochainComplex.Enriched.selfExtLinearMap
#check @CategoryTheory.CochainComplex.Enriched.ComputesSelfExt
#check @DifferentialGradedModule.Derived.regularSelfExtLinearMap
#check @Derived.regularSelfExt_comm
#check @Derived.regularComparison
#check @Derived.regularComparison_isIso
