/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Flat module lifts versus bounded-above derived lifts

This leaf owns the comparison between an underived `A'`-flat `P'`-module lift of `M`
and a bounded-above derived extension of scalars lift of `single0 M`.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right DerivedTensorWithAlgebra

universe u

namespace CategoryTheory.ModuleCat.NilpotentLift

/-- Existence of an `A'`-flat `P'`-module `M'` with
`(ModuleCat.extendScalars (algebraMap P' P)).obj M'` isomorphic to `M`. -/
def existsFlatLift (A' : Type u) [CommRing A'] (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P] [Algebra A' P']
    (M : ModuleCat.{u} P) : Prop :=
  ∃ M' : ModuleCat.{u} P',
    Module.Flat A' ((ModuleCat.restrictScalars (algebraMap A' P')).obj M') ∧
      IsIsomorphic ((ModuleCat.extendScalars (algebraMap P' P)).obj M') M

/-- Unfolding of `existsFlatLift`. -/
theorem existsFlatLift_iff (A' : Type u) [CommRing A'] (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P] [Algebra A' P']
    (M : ModuleCat.{u} P) :
    existsFlatLift A' P' M ↔
      ∃ M' : ModuleCat.{u} P',
        Module.Flat A' ((ModuleCat.restrictScalars (algebraMap A' P')).obj M') ∧
          IsIsomorphic ((ModuleCat.extendScalars (algebraMap P' P)).obj M') M :=
  sorry

/-- Existence of `K'` in `D⁻(ModuleCat P')` with `K' ⊗[P']^L[P]` isomorphic to `single0 M`. -/
def existsBoundedAboveDerivedLift (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P]
    (M : ModuleCat.{u} P) : Prop :=
  ∃ K' : DerivedCategory (ModuleCat.{u} P'),
    DerivedCategory.IsBoundedAbove K' ∧
      IsIsomorphic ((derivedExtensionOfScalars (algebraMap P' P)).obj K') (single0 M)

/-- Unfolding of `existsBoundedAboveDerivedLift`, using derived extension-of-scalars notation. -/
theorem existsBoundedAboveDerivedLift_iff (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P]
    (M : ModuleCat.{u} P) :
    existsBoundedAboveDerivedLift P' M ↔
      ∃ K' : DerivedCategory (ModuleCat.{u} P'),
        DerivedCategory.IsBoundedAbove K' ∧
          IsIsomorphic (K' ⊗[P']^L[P]) (single0 M) :=
  sorry

/-- If `A' → A` is surjective with nilpotent kernel, `A' → P'` is flat, and `M` is an
`A`-flat module over `P' ⊗[A'] A`, then an `A'`-flat `P'`-module lift of `M` exists if and
only if a bounded-above derived extension lift of `single0 M` exists. -/
theorem existsFlatLift_iff_existsBoundedAboveDerivedLift
    {A' A P' : Type u} [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P'] [Module.Flat A' P']
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (M : ModuleCat.{u} (P' ⊗[A'] A))
    (hMflat : Module.Flat A
      ((ModuleCat.restrictScalars (algebraMap A (P' ⊗[A'] A))).obj M)) :
    existsFlatLift A' P' M ↔ existsBoundedAboveDerivedLift P' M :=
  sorry

end CategoryTheory.ModuleCat.NilpotentLift

end
