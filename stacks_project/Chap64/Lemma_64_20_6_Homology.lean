module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap64.Lemma_64_20_6_ZModPow

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

namespace DerivedCategory.IsPerfect

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
variable (hK : ∀ n, (K n).IsPerfect)
variable (π : ∀ n, End (K n))
variable (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n)
variable (hπ : ∀ n,
    CommSq ((derivedBaseChange ℓ n).map (π (n + 1))) (φ n).hom (φ n).hom (π n))

/-- Homology of `K n` in degree `i`, restricted to a `ℤ_[ℓ]`-module along
`PadicInt.toZModPow (n + 1)`. -/
noncomputable def homologyStage (i : ℤ) (n : ℕ) : ModuleCat.{u} ℤ_[ℓ] :=
  (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 1))).obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) i).obj (K n))

/-- Unfolding of a homology stage as restriction of scalars of derived homology. -/
theorem homologyStage_eq (i : ℤ) (n : ℕ) :
    homologyStage K i n =
      (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 1))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) i).obj (K n)) :=
  sorry

/-- The successor transition of restricted homology, induced by the adjunction transpose of `φ n`. -/
noncomputable def homologyStep (i : ℤ) (n : ℕ) :
    homologyStage K i (n + 1) ⟶ homologyStage K i n :=
  (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 2))).map
      (homologyUntranspose (zmodPowStepHom ℓ n) (φ n).hom i) ≫
    (ModuleCat.restrictScalarsComp'
        (PadicInt.toZModPow (n + 2)) (zmodPowStepHom ℓ n) (PadicInt.toZModPow (n + 1))
        (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1))).symm).inv.app _

/-- The sequential inverse system `{H^i(K_n)}` of `ℤ_[ℓ]`-modules. -/
noncomputable def homologySystem (i : ℤ) : SequentialInverseSystem (ModuleCat.{u} ℤ_[ℓ]) :=
  Functor.ofOpSequence (homologyStep K φ i)

/-- Stage `n` of the homology inverse system is the restricted homology of `K n`. -/
theorem homologySystem_obj (i : ℤ) (n : ℕ) :
    (homologySystem K φ i).obj (op n) = homologyStage K i n := sorry

/-- Successor transitions of the homology inverse system are `homologyStep`. -/
theorem homologySystem_map (i : ℤ) (n : ℕ) :
    (homologySystem K φ i).stepMap n = homologyStep K φ i n := sorry

/-- Inverse-limit homology `H_∞^i = lim H^i(K_n)` as a `ℤ_[ℓ]`-module. -/
noncomputable def homologyLimit (i : ℤ) : ModuleCat.{u} ℤ_[ℓ] :=
  limit (homologySystem K φ i)

/-- Unfolding of inverse-limit homology as the categorical limit of `homologySystem`. -/
theorem homologyLimit_eq (i : ℤ) :
    homologyLimit K φ i = limit (homologySystem K φ i) := sorry

/-- Projection from inverse-limit homology onto the restricted homology of a stage. -/
noncomputable def homologyLimit_π (i : ℤ) (n : ℕ) :
    homologyLimit K φ i ⟶ homologyStage K i n :=
  limit.π (homologySystem K φ i) (op n)

/-- The cone projection of inverse-limit homology is the inverse-limit projection of
`homologySystem`. -/
theorem homologyLimit_π_eq (i : ℤ) (n : ℕ) :
    homologyLimit_π K φ i n = limit.π (homologySystem K φ i) (op n) := sorry

/-- The endomorphism of a homology stage induced by `π n`. -/
noncomputable def homologyStageEnd (i : ℤ) (n : ℕ) :
    homologyStage K i n ⟶ homologyStage K i n :=
  (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 1))).map
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) i).map (π n))

/-- Unfolding of the stage endomorphism as restriction of scalars of `H^i(π_n)`. -/
theorem homologyStageEnd_eq (i : ℤ) (n : ℕ) :
    homologyStageEnd K π i n =
      (ModuleCat.restrictScalars (PadicInt.toZModPow (n + 1))).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) i).map (π n)) :=
  sorry

/-- The cone presenting the inverse-limit endomorphism induced by the compatible
family `{H^i(π_n)}`. -/
noncomputable def homologyLimitEndCone
    (hπ : ∀ n, CommSq ((derivedBaseChange ℓ n).map (π (n + 1))) (φ n).hom (φ n).hom (π n))
    (i : ℤ) : Cone (homologySystem K φ i) where
  pt := homologyLimit K φ i
  π :=
    { app := fun n => homologyLimit_π K φ i n.unop ≫ homologyStageEnd K π i n.unop
      naturality := sorry }

/-- The induced endomorphism `π_∞^i` of inverse-limit homology. -/
noncomputable def homologyLimitEnd (i : ℤ) : End (homologyLimit K φ i) :=
  limit.lift (homologySystem K φ i) (homologyLimitEndCone K π φ hπ i)

/-- The inverse-limit endomorphism commutes with the stage projections. -/
theorem homologyLimitEnd_comp_π (i : ℤ) (n : ℕ) :
    homologyLimitEnd K π φ hπ i ≫ homologyLimit_π K φ i n =
      homologyLimit_π K φ i n ≫ homologyStageEnd K π i n := sorry

/-- Extension of scalars of inverse-limit homology from `ℤ_[ℓ]` to `ℚ_[ℓ]`. -/
noncomputable def homologyLimitQEll (i : ℤ) : ModuleCat.{u} ℚ_[ℓ] :=
  (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj (homologyLimit K φ i)

/-- Unfolding of `ℚ_[ℓ]`-homology as extension of scalars of `homologyLimit`. -/
theorem homologyLimitQEll_eq (i : ℤ) :
    homologyLimitQEll K φ i =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj (homologyLimit K φ i) := sorry

/-- The endomorphism `π_∞^i ⊗ ℚ_[ℓ]` of inverse-limit homology after extending scalars. -/
noncomputable def homologyLimitEndQEll (i : ℤ) :
    Module.End ℚ_[ℓ] (homologyLimitQEll K φ i) :=
  ModuleCat.Hom.hom ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (homologyLimitEnd K π φ hπ i))

/-- Unfolding of `homologyLimitEndQEll` as the linear map underlying the scalar extension of
`homologyLimitEnd`. -/
theorem homologyLimitEndQEll_spec (i : ℤ) :
    homologyLimitEndQEll K π φ hπ i =
      ModuleCat.Hom.hom ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (homologyLimitEnd K π φ hπ i)) := sorry

include hK in
/-- Inverse-limit homology becomes finite-dimensional after extending scalars to `ℚ_[ℓ]`. -/
theorem finiteDimensional_homologyLimitEndQEll (i : ℤ) :
    FiniteDimensional ℚ_[ℓ] (homologyLimitQEll K φ i) := sorry

end DerivedCategory.IsPerfect

