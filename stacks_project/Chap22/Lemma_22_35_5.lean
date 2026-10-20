module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open SheafOfModules.RingedSite.TensorWithObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (K : Complex (J := J) (O := O))

/- Lemma 22.35.5 (09LY): for a complex `K` on a ringed site, derived tensoring with `K` over
`endDGA K` is left adjoint to the concrete derived representable functor `RHom(K, -)`. -/
@[stacks 09LY] #check
  (Derived.adjunction K : Derived.tensorFunctor K ⊣ Derived.representableFunctor K)

#check @Derived.representableFunctor
#check @Derived.representableUnit
#check @Derived.homEquiv
