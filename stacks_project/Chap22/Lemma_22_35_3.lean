module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Functor
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TensorWithObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (K : Complex (J := J) (O := O))

/- Lemma 22.35.3 (09LX): the concrete tensor DG functor associated to a complex `K` on a
ringed site has a total left-derived functor on `D(endDGA K)`. -/
@[stacks 09LX] #check
  (Derived.tensorFunctor K :
    DifferentialGradedModule.Derived.Category (endDGA K) ⥤
      RingedSiteDerived.max J O)

#check @Derived.tensorSourceFunctor
#check @Derived.HasTensorFunctor
#check @Derived.tensorCounit
