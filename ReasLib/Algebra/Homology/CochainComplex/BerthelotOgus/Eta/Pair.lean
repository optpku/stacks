module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Reduction
public import ReasLib.LinearAlgebra.ProductRange

/-!
# The pair map of the nonnegative Berthelot-Ogus eta complex

For a nonnegative cochain complex, the degree-`n` eta term maps by `(1, d)` to the product of the
visible power submodules `f^n K^n` and `f^(n+1) K^(n+1)`.  This file owns that map and its reduction
modulo `(f)`.  The integer-indexed divided-differential coordinate version lives in `Eta.Int.Pair`.
@stack 0F7Z
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

/-- The visible power submodule `f^n K^n`. -/
abbrev powerSubmodule (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Submodule A (K.X n) :=
  principalIdeal (f ^ n) • (⊤ : Submodule A (K.X n))

/-- The visible next-degree power submodule `f^(n+1) K^(n+1)`. -/
abbrev nextPowerSubmodule (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Submodule A (K.X (n + 1)) :=
  principalIdeal (f ^ (n + 1)) • (⊤ : Submodule A (K.X (n + 1)))

/-- The degree-`n` eta term is contained in `f^n K^n`. -/
theorem term_le_powerSubmodule
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    term f K n ≤ powerSubmodule f K n := sorry

/-- The eta differential, with codomain restricted to `f^(n+1) K^(n+1)`. -/
def differentialToNextPower
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    term f K n →ₗ[A] nextPowerSubmodule f K n :=
  (Submodule.inclusion (term_le_powerSubmodule f K (n + 1))) ∘ₗ
    ((eta f K).d n (n + 1)).hom

/-- The visible-power pair `(1, d)` on a term of the nonnegative eta complex. -/
@[stacks 0F7Z "visible-power Berthelot-Ogus eta pair"]
def pairLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    term f K n →ₗ[A] powerSubmodule f K n × nextPowerSubmodule f K n :=
  LinearMap.prod (Submodule.inclusion (term_le_powerSubmodule f K n))
    (differentialToNextPower f K n)

/-- Evaluation of the visible-power pair map is the pair formed by inclusion and the eta
differential. -/
@[simp]
theorem pairLinear_apply (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) (x : term f K n) :
    pairLinear f K n x =
      (Submodule.inclusion (term_le_powerSubmodule f K n) x,
        differentialToNextPower f K n x) := sorry

/-- First projection of the pair map is the inclusion into the visible power submodule. -/
@[simp]
theorem fst_comp_pairLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (LinearMap.fst A (powerSubmodule f K n) (nextPowerSubmodule f K n)).comp
        (pairLinear f K n) =
      Submodule.inclusion (term_le_powerSubmodule f K n) := sorry

/-- Second projection of the pair map is the eta differential with restricted codomain. -/
@[simp]
theorem snd_comp_pairLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (LinearMap.snd A (powerSubmodule f K n) (nextPowerSubmodule f K n)).comp
        (pairLinear f K n) = differentialToNextPower f K n := sorry

/-- The visible-power pair map is injective. -/
theorem pairLinear_injective (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Function.Injective (pairLinear f K n) := sorry

/-- The visible-power pair map is a monomorphism in `ModuleCat`. -/
instance pairLinear_mono (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Mono (ModuleCat.ofHom (pairLinear f K n)) := sorry

end CochainComplex.BerthelotOgus.Nat.Pair

namespace CochainComplex.BerthelotOgus.Nat.Reduction.Pair

open CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

/-- The first visible power submodule reduced modulo `(f)`. -/
abbrev powerQuotient
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :=
  powerSubmodule f K n ⧸
    principalIdeal f • (⊤ : Submodule A (powerSubmodule f K n))

/-- The next visible power submodule reduced modulo `(f)`. -/
abbrev nextPowerQuotient
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :=
  nextPowerSubmodule f K n ⧸
    principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f K n))

/-- The reduction modulo `(f)` of the visible-power eta pair. -/
@[stacks 0F7Z "reduced visible-power Berthelot-Ogus eta pair"]
noncomputable def reducedPairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (complex f K).X n →ₗ[A ⧸ principalIdeal f]
      powerQuotient f K n × nextPowerQuotient f K n :=
  LinearMap.prod
    (LinearMap.IdealQuotient.map
      (Submodule.inclusion (term_le_powerSubmodule f K n)) (principalIdeal f))
    (LinearMap.IdealQuotient.map (differentialToNextPower f K n) (principalIdeal f))

/-- On a quotient generator, the first coordinate is the visible-power inclusion modulo `f`. -/
theorem reducedPairLinear_fst_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) (x : term f K n) :
    (reducedPairLinear f K n (Submodule.Quotient.mk x)).1 =
      Submodule.Quotient.mk (Submodule.inclusion (term_le_powerSubmodule f K n) x) := sorry

/-- On a quotient generator, the second coordinate is the eta differential modulo `f`. -/
theorem reducedPairLinear_snd_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) (x : term f K n) :
    (reducedPairLinear f K n (Submodule.Quotient.mk x)).2 =
      Submodule.Quotient.mk (differentialToNextPower f K n x) := sorry

end CochainComplex.BerthelotOgus.Nat.Reduction.Pair
