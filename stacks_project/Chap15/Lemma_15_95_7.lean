module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.TensorPseudoCoherent
import StacksCheckRecall

/-!
# Derived completion and pseudo-coherent tensor factors

@stack 0EEV
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

-- Local instance justification (search instability): expose the standard
-- derived localization only while spelling the tensor-completion comparisons.
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DModMinus" => DerivedCategory.Minus (ModuleCat A)

/- Lemma 15.95.7 (1): completion of a bounded-above complex commutes with derived tensoring by a
finite module placed in degree zero. -/
section

variable (K : DModMinus) (M : ModuleCat A) (hM : Module.Finite A M)

#check fun (I : Ideal A) ↦
  (DerivedCategory.DerivedCompletion.Tensor.moduleComparison I K M hM :
    ((K.obj ⊗[A]^L ModuleCat.single0Functor.obj M)^∧[
        I, I.fg_of_isNoetherianRing]) ⟶
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L
        ModuleCat.single0Functor.obj M))

@[stacks 0EEV "(1), completion commutes with finite module tensor factors"]
#check fun (I : Ideal A) ↦
  (DerivedCategory.DerivedCompletion.Tensor.moduleComparison_isIso I K M hM :
    IsIso (DerivedCategory.DerivedCompletion.Tensor.moduleComparison I K M hM))

#check fun (I : Ideal A) ↦
  (DerivedCategory.DerivedCompletion.Tensor.toDerivedCompletion_comp_moduleComparison
      I K M hM :
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
          (K.obj ⊗[A]^L ModuleCat.single0Functor.obj M) ≫
        DerivedCategory.DerivedCompletion.Tensor.moduleComparison I K M hM =
      (CategoryTheory.DerivedCategory.DerivedTensor.Right.functor
          (ModuleCat.single0Functor.obj M)).map
        (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K.obj))

end

/- Lemma 15.95.7 (2): completion of a bounded-above complex commutes with derived tensoring by a
pseudo-coherent complex. -/
section

variable (K : DModMinus) (L : DMod) (hL : L.IsPseudoCoherent)

#check fun (I : Ideal A) ↦
  (DerivedCategory.DerivedCompletion.Tensor.comparison I K L hL :
    ((K.obj ⊗[A]^L L)^∧[I, I.fg_of_isNoetherianRing]) ⟶
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L L))

@[stacks 0EEV "(2), completion commutes with pseudo-coherent derived tensor factors"]
#check fun (I : Ideal A) ↦
  (DerivedCategory.DerivedCompletion.Tensor.comparison_isIso I K L hL :
    IsIso (DerivedCategory.DerivedCompletion.Tensor.comparison I K L hL))

#check fun (I : Ideal A) ↦
  (DerivedCategory.DerivedCompletion.Tensor.toDerivedCompletion_comp_comparison I K L hL :
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
          (K.obj ⊗[A]^L L) ≫
        DerivedCategory.DerivedCompletion.Tensor.comparison I K L hL =
      (CategoryTheory.DerivedCategory.DerivedTensor.Right.functor L).map
        (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K.obj))

end
