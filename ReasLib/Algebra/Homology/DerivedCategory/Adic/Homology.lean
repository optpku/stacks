module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.Algebra.Homology.DerivedCategory.Adic.ZModPow
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology

/-!
# Inverse-limit homology of a Cartesian system of perfect complexes

The `ℤ_[ℓ]`-modules `H_∞^i = lim H^i(K_n)` attached to a compatible family of
perfect complexes over `ZMod (ℓ ^ (n + 1))`, together with the induced
endomorphisms `π_∞^i` and their extensions of scalars to `ℚ_[ℓ]`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.DerivedCategory.IsPerfect

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
variable (π : ∀ n, End (K n))
variable (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n)
variable (hπ : ∀ n,
    CommSq ((derivedBaseChange ℓ n).map (π (n + 1))) (φ n).hom (φ n).hom (π n))

/-- Homology of `K n` in degree `i`, restricted to a `ℤ_[ℓ]`-module along
`PadicInt.toZModPow (n + 1)`. -/
noncomputable def homologyStage (i : ℤ) (n : ℕ) : ModuleCat.{u} ℤ_[ℓ] :=
  (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 1))).obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) i).obj (K n))

/-- The successor transition of restricted homology, induced by the adjunction transpose of `φ n`. -/
noncomputable def homologyStep (i : ℤ) (n : ℕ) :
    homologyStage K i (n + 1) ⟶ homologyStage K i n :=
  (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 2))).map
      (ModuleCat.homologyUntranspose (zmodPowStepHom ℓ n) (φ n).hom i) ≫
    (ModuleCat.restrictScalarsComp'
        (PadicInt.toZModPow (n + 2)) (zmodPowStepHom ℓ n) (PadicInt.toZModPow (n + 1))
        (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1))).symm).inv.app _

/-- The sequential inverse system `{H^i(K_n)}` of `ℤ_[ℓ]`-modules. -/
noncomputable def homologySystem (i : ℤ) : SequentialInverseSystem (ModuleCat.{u} ℤ_[ℓ]) :=
  Functor.ofOpSequence (homologyStep K φ i)

/-- Stage `n` of the homology inverse system is the restricted homology of `K n`. -/
theorem homologySystem_obj (i : ℤ) (n : ℕ) :
    (homologySystem K φ i).obj (op n) = homologyStage K i n := rfl

/-- Successor transitions of the homology inverse system are `homologyStep`. -/
theorem homologySystem_map (i : ℤ) (n : ℕ) :
    (homologySystem K φ i).stepMap n = homologyStep K φ i n :=
  Functor.ofOpSequence_map_homOfLE_succ (homologyStep K φ i) n

/-- Inverse-limit homology `H_∞^i = lim H^i(K_n)` as a `ℤ_[ℓ]`-module. -/
noncomputable def homologyLimit (i : ℤ) : ModuleCat.{u} ℤ_[ℓ] :=
  limit (homologySystem K φ i)

/-- Projection from inverse-limit homology onto the restricted homology of a stage. -/
noncomputable def homologyLimit_π (i : ℤ) (n : ℕ) :
    homologyLimit K φ i ⟶ homologyStage K i n :=
  limit.π (homologySystem K φ i) (op n)

/-- The endomorphism of a homology stage induced by `π n`. -/
noncomputable def homologyStageEnd (i : ℤ) (n : ℕ) :
    homologyStage K i n ⟶ homologyStage K i n :=
  (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 1))).map
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) i).map (π n))

include hπ in
/-- The cohomology endomorphisms commute with the successor transitions of a compatible
Cartesian derived tower. -/
theorem homologyStageEnd_naturality (i : ℤ) (n : ℕ) :
    homologyStep K φ i n ≫ homologyStageEnd K π i n =
      homologyStageEnd K π i (n + 1) ≫ homologyStep K φ i n := sorry

/-- The endomorphism of the cohomology inverse system induced by compatible derived
endomorphisms. -/
noncomputable def homologySystemEnd (i : ℤ) : End (homologySystem K φ i) :=
  NatTrans.ofOpSequence (F := homologySystem K φ i) (G := homologySystem K φ i)
    (homologyStageEnd K π i) (fun n => by
      change (homologySystem K φ i).stepMap n ≫ homologyStageEnd K π i n =
        homologyStageEnd K π i (n + 1) ≫ (homologySystem K φ i).stepMap n
      rw [homologySystem_map]
      exact homologyStageEnd_naturality K π φ hπ i n)

/-- The induced endomorphism `π_∞^i` of inverse-limit homology. -/
noncomputable def homologyLimitEnd (i : ℤ) : End (homologyLimit K φ i) :=
  (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} ℤ_[ℓ]) ⥤ ModuleCat.{u} ℤ_[ℓ]).map
    (homologySystemEnd K π φ hπ i)

/-- The inverse-limit endomorphism commutes with the stage projections. -/
theorem homologyLimitEnd_comp_π (i : ℤ) (n : ℕ) :
    homologyLimitEnd K π φ hπ i ≫ homologyLimit_π K φ i n =
      homologyLimit_π K φ i n ≫ homologyStageEnd K π i n := sorry

/-- Extension of scalars of inverse-limit homology from `ℤ_[ℓ]` to `ℚ_[ℓ]`. -/
noncomputable def homologyLimitQEll (i : ℤ) : ModuleCat.{u} ℚ_[ℓ] :=
  (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj (homologyLimit K φ i)

/-- The endomorphism `π_∞^i ⊗ ℚ_[ℓ]` of inverse-limit homology after extending scalars. -/
noncomputable def homologyLimitEndQEll (i : ℤ) :
    Module.End ℚ_[ℓ] (homologyLimitQEll K φ i) :=
  ModuleCat.Hom.hom ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (homologyLimitEnd K π φ hπ i))

end CategoryTheory.DerivedCategory.IsPerfect
