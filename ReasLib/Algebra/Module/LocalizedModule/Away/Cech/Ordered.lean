/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Augment
public import ReasLib.Algebra.Module.LocalizedModule.Away.Map
public import ReasLib.AlgebraicTopology.Cech.OrderedIndex

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace LocalizedModule.Away.Cech.Ordered

variable {R : Type u} [CommRing R]
variable {r : ℕ}

section

variable (f : Fin r → R)

/-- The denominator obtained by multiplying the entries of an increasing Čech tuple. -/
def denominator {p : ℕ} (σ : OrderedCechIndex (Fin r) p) : R :=
  ∏ j, f (σ j)

/-- Deleting one entry from an increasing tuple gives a divisor of its denominator. -/
theorem denominator_delete_dvd (p : ℕ) (σ : OrderedCechIndex (Fin r) (p + 1))
    (j : Fin (p + 2)) : denominator f (σ.delete j) ∣ denominator f σ := sorry

/-- The degree-`p` ordered Čech term with coefficients in `M`. -/
def term (M : Type (max u v)) [AddCommGroup M] [Module R M] (p : ℕ) :
    ModuleCat.{max u v} R :=
  ModuleCat.of R (∀ σ : OrderedCechIndex (Fin r) p, LocalizedModule.Away (denominator f σ) M)

/-- The restriction map associated to deletion of one entry of an increasing tuple. -/
noncomputable def coface (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (p : ℕ) (j : Fin (p + 2)) : term f M p ⟶ term f M (p + 1) :=
  ModuleCat.ofHom (LinearMap.pi fun σ ↦
    (LocalizedModule.Away.mapOfDvd (denominator f (σ.delete j)) (denominator f σ)
      (denominator_delete_dvd f p σ j)).comp (LinearMap.proj (σ.delete j)))

/-- The alternating signed sum of ordered localization cofaces. -/
noncomputable def differential (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (p : ℕ) : term f M p ⟶ term f M (p + 1) :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • coface f M p j

/-- The ordered Čech differential has the coordinatewise alternating formula. -/
theorem differential_apply (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (p : ℕ) (x : term f M p) (σ : OrderedCechIndex (Fin r) (p + 1)) :
    (differential f M p).hom x σ =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        LocalizedModule.Away.mapOfDvd (denominator f (σ.delete j)) (denominator f σ)
          (denominator_delete_dvd f p σ j) (x (σ.delete j)) := sorry

/-- Consecutive ordered Čech differentials compose to zero. -/
theorem differential_comp (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (p : ℕ) : differential f M p ≫ differential f M (p + 1) = 0 := sorry

/-- The degree-zero augmentation into the product of localizations at the generators. -/
noncomputable def augmentationMap (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    ModuleCat.of R M ⟶ term f M 0 :=
  ModuleCat.ofHom (LinearMap.pi fun σ ↦
    LocalizedModule.mkLinearMap (Submonoid.powers (denominator f σ)) M)

/-- The augmentation is killed by the first ordered Čech differential. -/
theorem augmentationMap_comp_differential (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    augmentationMap f M ≫ differential f M 0 = 0 := sorry

/-- The augmented ordered Čech complex in nonnegative degrees. -/
noncomputable def complex (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of (term f M) (differential f M) (differential_comp f M)

/-- The canonical augmentation from the degree-zero single complex to the ordered Čech complex. -/
noncomputable def augmentation (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj (ModuleCat.of R M) ⟶ complex f M :=
  (CochainComplex.fromSingle₀Equiv (complex f M) (ModuleCat.of R M)).symm
    ⟨augmentationMap f M, augmentationMap_comp_differential f M⟩

/-- The ordered Čech complex with the coefficient module in degree zero. -/
noncomputable def extended (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.fromSingle₀AsComplex (complex f M) (ModuleCat.of R M) (augmentation f M)

/-- The degree-zero object of the augmented ordered Čech complex. -/
theorem extended_X_zero (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    (extended f M).X 0 = ModuleCat.of R M := sorry

/-- The positive-degree objects of the augmented ordered Čech complex are ordered localization
products. -/
theorem extended_X_succ (M : Type (max u v)) [AddCommGroup M] [Module R M] (p : ℕ) :
    (extended f M).X (p + 1) = term f M p := sorry

end

end LocalizedModule.Away.Cech.Ordered
