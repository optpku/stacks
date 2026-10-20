/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Single
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext groups into a field via homology of derived scalar extension

For a ring map `σ : A →+* k` with `k` a field and `E` in `D⁻(ModuleCat A)`,
the groups `Ext^i_A(E, k)` are identified with
`Hom_k(H^{-i}(E ⊗^L k), k)` by a canonical comparison on derived categories.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory
open DerivedCategory.ShiftedHom.Boundary

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.Ext

variable {A k : Type u} [CommRing A] [Field k]

/-- The derived Ext group `Ext^i_A(E, k)`, realized as shifted morphisms in
`D(ModuleCat A)` from `E` into the restriction of scalars of `k` placed in
degree `0`. -/
abbrev extIntoField (σ : A →+* k) (E : Minus (ModuleCat.{u} A)) (i : ℤ) :=
  ShiftedHom (Minus.ι.obj E)
    ((singleFunctor (ModuleCat A) 0).obj
      ((ModuleCat.restrictScalars σ).obj (ModuleCat.of k k))) i

/-- Morphisms `H^{-i}(E ⊗^L k) ⟶ k` in `ModuleCat k`, where `E ⊗^L k` is
derived extension of scalars along `σ`. -/
abbrev homologyDual (σ : A →+* k) (E : Minus (ModuleCat.{u} A)) (i : ℤ) :=
  (homologyFunctor (ModuleCat k) (-i)).obj
      ((ModuleCat.derivedExtensionOfScalars σ).obj (Minus.ι.obj E)) ⟶
    ModuleCat.of k k

/-- The canonical comparison `Ext^i_A(E, k) → Hom_k(H^{-i}(E ⊗^L k), k)`.

The map transports the target along `DerivedRestriction.singleIso`, applies
the derived extension-restriction adjunction, takes the t-structure boundary
map to homology in degrees `-i` and `0`, and identifies `H^0(k[0])` with `k`. -/
def extToHomologyDual (σ : A →+* k) (E : Minus (ModuleCat.{u} A)) (i : ℤ) :
    extIntoField σ E i → homologyDual σ E i :=
  fun f ↦
    let kObj := ModuleCat.of k k
    let kSingle := (singleFunctor (ModuleCat k) 0).obj kObj
    let Eobj := Minus.ι.obj E
    let degreeEq : i = (0 : ℤ) - (-i) :=
      (Eq.trans (Int.zero_sub (-i)) (Int.neg_neg i)).symm
    let fExtended :
        ShiftedHom ((ModuleCat.derivedExtensionOfScalars σ).obj Eobj)
          kSingle ((0 : ℤ) - (-i)) :=
      (ModuleCat.derivedExtensionRestrictionAdjunction σ).shiftedHomEquiv
          Eobj kSingle i
          (f ≫ ((ModuleCat.DerivedRestriction.singleIso σ 0 kObj).inv)⟦i⟧') ≫
        eqToHom (congrArg (fun n : ℤ ↦ kSingle⟦n⟧) degreeEq)
    toHomology ((ModuleCat.derivedExtensionOfScalars σ).obj Eobj) kSingle
        (-i) 0 fExtended ≫
      (singleFunctorCompHomologyFunctorIso (ModuleCat k) 0).hom.app kObj

/-- Evaluation of `extToHomologyDual` is the composed comparison through
restriction, the derived adjunction, and the homology boundary map. -/
@[simp]
theorem extToHomologyDual_apply (σ : A →+* k) (E : Minus (ModuleCat.{u} A))
    (i : ℤ) (f : extIntoField σ E i) :
    extToHomologyDual σ E i f =
      let kObj := ModuleCat.of k k
      let kSingle := (singleFunctor (ModuleCat k) 0).obj kObj
      let Eobj := Minus.ι.obj E
      let degreeEq : i = (0 : ℤ) - (-i) :=
        (Eq.trans (Int.zero_sub (-i)) (Int.neg_neg i)).symm
      let fExtended :
          ShiftedHom ((ModuleCat.derivedExtensionOfScalars σ).obj Eobj)
            kSingle ((0 : ℤ) - (-i)) :=
        (ModuleCat.derivedExtensionRestrictionAdjunction σ).shiftedHomEquiv
            Eobj kSingle i
            (f ≫ ((ModuleCat.DerivedRestriction.singleIso σ 0 kObj).inv)⟦i⟧') ≫
          eqToHom (congrArg (fun n : ℤ ↦ kSingle⟦n⟧) degreeEq)
      toHomology ((ModuleCat.derivedExtensionOfScalars σ).obj Eobj) kSingle
          (-i) 0 fExtended ≫
        (singleFunctorCompHomologyFunctorIso (ModuleCat k) 0).hom.app kObj := sorry

/-- The comparison `extToHomologyDual` is additive on shifted Hom groups. -/
theorem extToHomologyDual_map_add (σ : A →+* k) (E : Minus (ModuleCat.{u} A))
    (i : ℤ) (f g : extIntoField σ E i) :
    extToHomologyDual σ E i (f + g) =
      extToHomologyDual σ E i f + extToHomologyDual σ E i g := sorry

/-- For a ring map `σ : A →+* k` to a field and a bounded-above derived
`A`-module `E`, the canonical comparison from `Ext^i_A(E, k)` to
`Hom_k(H^{-i}(E ⊗^L k), k)` is bijective in every integer degree. -/
@[stacks 07YK]
theorem extToHomologyDual_bijective (σ : A →+* k)
    (E : Minus (ModuleCat.{u} A)) (i : ℤ) :
    Function.Bijective (extToHomologyDual σ E i) := sorry

end CategoryTheory.DerivedCategory.Ext
