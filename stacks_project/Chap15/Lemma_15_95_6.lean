/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion
import StacksCheckRecall

/-!
# Derived completion of finite-flat tensors and localizations

@stack 0EEU
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

-- Local instance justification (search instability): expose the standard
-- derived localization only while spelling the comparison morphisms.
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

section

variable (M : Type u) [AddCommGroup M] [Module A M]

/- The comparison map is the universal derived-completion lift of the ordinary completion map. -/
#check fun (I : Ideal A) (hI : I.FG) ↦
  (DerivedCategory.DerivedCompletion.Adic.comparison I hI M :
    DerivedCategory.derivedCompletionOf I hI
        ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj (ModuleCat.of A M)) ⟶
      (ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj
        (ModuleCat.of A (AdicCompletion I M)))

#check fun (I : Ideal A) (hI : I.FG) ↦
  (DerivedCategory.DerivedCompletion.Adic.toDerivedCompletion_comp_comparison I hI M :
    DerivedCategory.toDerivedCompletion I hI
          ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj (ModuleCat.of A M)) ≫
        DerivedCategory.DerivedCompletion.Adic.comparison I hI M =
      (ModuleCat.single0Functor : ModuleCat A ⥤ DMod).map
        (ModuleCat.ofHom (AdicCompletion.of I M) :
          ModuleCat.of A M ⟶ ModuleCat.of A (AdicCompletion I M)))

end

/- Lemma 15.95.6 (1): for a finite module `M` and flat module `N`, derived completion of
`(M ⊗[A] N)[0]` is the degree-zero object on its ordinary adic completion. -/
section

variable (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N]

@[stacks 0EEU "(1), finite-flat tensor derived completion"]
#check fun (I : Ideal A) (hI : I.FG) ↦
  (DerivedCategory.DerivedCompletion.Adic.comparison_isIso_of_finite_tensor_flat
      I hI M N :
    IsIso (DerivedCategory.DerivedCompletion.Adic.comparison I hI (M ⊗[A] N)))

end

/- Lemma 15.95.6 (2): derived completion of the localization of a finite module is the
degree-zero object on its ordinary adic completion. -/
section

variable (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

@[stacks 0EEU "(2), localized finite module derived completion"]
#check fun (I : Ideal A) (hI : I.FG) (f : A) ↦
  (DerivedCategory.DerivedCompletion.Adic.comparison_isIso_localizationAway_of_finite
      I hI M f :
    IsIso
      (DerivedCategory.DerivedCompletion.Adic.comparison
        I hI (LocalizedModule.Away f M)))

end
