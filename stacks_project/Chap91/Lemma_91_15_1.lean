/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.SquareZeroExtension
import StacksCheckRecall

/-!
# Canonical obstruction for lifting a bounded-above derived module

The degree-two obstruction vanishes exactly when the object lifts across the square-zero
surjection. It is natural and is compatible with arbitrary ring base change.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 91.15.1. A square-zero surjection has a canonical degree-two obstruction
for every bounded-above derived module. -/
@[stacks 0DYR] #check (ModuleCat.SquareZeroExtension.canonicalClass :
  ∀ {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove),
    K ⟶ ModuleCat.SquareZeroExtension.tensorKernelShift f K)

#check (ModuleCat.SquareZeroExtension.canonicalClass_eq_zero_iff :
  ∀ {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove),
    ModuleCat.SquareZeroExtension.canonicalClass f K hK = 0 ↔
      ∃ K' : DerivedCategory (ModuleCat.{u} R'),
        IsIsomorphic ((ModuleCat.derivedExtensionOfScalars f).obj K') K)

#check (ModuleCat.SquareZeroExtension.canonicalClass_natural :
  ∀ {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) [f.IsSquareZeroExtension]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (hK : K.IsBoundedAbove) (hL : L.IsBoundedAbove) (α : K ⟶ L),
    ModuleCat.SquareZeroExtension.canonicalClass f K hK ≫
        ModuleCat.SquareZeroExtension.tensorKernelShiftMap f α =
      α ≫ ModuleCat.SquareZeroExtension.canonicalClass f L hL)

#check (ModuleCat.SquareZeroExtension.canonicalClass_baseChange :
  ∀ {R' R : Type u} [CommRing R'] [CommRing R]
    {S' : Type u} [CommRing S']
    (f : R' →+* R) [f.IsSquareZeroExtension] (g : R' →+* S')
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove),
    (ModuleCat.derivedExtensionOfScalars
        (ModuleCat.SquareZeroExtension.tensorCodomainIncludeRight f g)).map
          (ModuleCat.SquareZeroExtension.canonicalClass f K hK) ≫
        ModuleCat.SquareZeroExtension.kernelBaseChangeDerived f g K =
      ModuleCat.SquareZeroExtension.canonicalClass
        (ModuleCat.SquareZeroExtension.tensorCodomainRingHom f g)
        ((ModuleCat.derivedExtensionOfScalars
          (ModuleCat.SquareZeroExtension.tensorCodomainIncludeRight f g)).obj K)
        (CategoryTheory.ModuleCat.derivedExtensionOfScalars_isBoundedAbove
          (ModuleCat.SquareZeroExtension.tensorCodomainIncludeRight f g) K hK))
