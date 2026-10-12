/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Cohomology
import StacksCheckRecall

/-!
# Cohomology of derived completion over a Noetherian ring

@stack 0A06
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

-- Local instance justification (search instability): expose the standard
-- derived localization only while spelling the cohomology comparison types.
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Lemma 15.95.4: when every cohomology module of `K` is finite, `H^n(K^∧)` is canonically the
ordinary adic completion of `H^n(K)`. -/
#check fun (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) ↦
  (DerivedCategory.DerivedCompletion.Cohomology.comparison I K n hK :
    ModuleCat.of A (AdicCompletion I ((H n).obj K)) ⟶
      (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]))

@[stacks 0A06 "cohomology of Noetherian derived completion"]
#check fun (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) ↦
  (DerivedCategory.DerivedCompletion.Cohomology.comparison_isIso I K n hK :
    IsIso (DerivedCategory.DerivedCompletion.Cohomology.comparison I K n hK))

#check fun (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) ↦
  (DerivedCategory.DerivedCompletion.Cohomology.iso I K n hK :
    (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]) ≅
      ModuleCat.of A (AdicCompletion I ((H n).obj K)))

#check fun (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) ↦
  (DerivedCategory.DerivedCompletion.Cohomology.of_comp_comparison I K n hK :
    ModuleCat.ofHom (AdicCompletion.of I ((H n).obj K)) ≫
        DerivedCategory.DerivedCompletion.Cohomology.comparison I K n hK =
      (H n).map
        (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K))
