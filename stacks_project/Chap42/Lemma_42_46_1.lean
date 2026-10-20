/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Complex
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.46.1: the characteristic classes of a locally bounded, termwise finite
locally free complex depend only on the derived module that it represents. -/
@[stacks 0ESZ] #check
  (AlgebraicGeometry.ChernClass.Complex.totalClass_eq_of_representatives :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (π : X ⟶ S) [LocallyOfFiniteType π]
      (classes : AlgebraicGeometry.ChernClass.Theory δ π)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (K L : CochainComplex X.Modules ℤ)
      (hKAbove : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
      (hKBelow : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
      (hKFree : ∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (K.X n))
      (hKRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
      (hLAbove : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove L)
      (hLBelow : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedBelow L)
      (hLFree : ∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (L.X n))
      (hLRep : IsIsomorphic (DerivedCategory.Q.obj L) E),
      AlgebraicGeometry.ChernClass.Complex.totalClass δ π classes K
          hKAbove hKBelow hKFree =
        AlgebraicGeometry.ChernClass.Complex.totalClass δ π classes L
          hLAbove hLBelow hLFree)

/- The same representative-independence statement for the Chern-character family. -/
#check
  (AlgebraicGeometry.ChernClass.Complex.character_eq_of_representatives :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (π : X ⟶ S) [LocallyOfFiniteType π]
      (classes : AlgebraicGeometry.ChernClass.Theory δ π)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (K L : CochainComplex X.Modules ℤ)
      (hKAbove : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
      (hKBelow : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
      (hKFree : ∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (K.X n))
      (hKRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
      (hLAbove : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove L)
      (hLBelow : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedBelow L)
      (hLFree : ∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (L.X n))
      (hLRep : IsIsomorphic (DerivedCategory.Q.obj L) E),
      AlgebraicGeometry.ChernClass.Complex.character δ π classes K
          hKAbove hKBelow hKFree =
        AlgebraicGeometry.ChernClass.Complex.character δ π classes L
          hLAbove hLBelow hLFree)

/- The same representative-independence statement in every integral Newton degree. -/
#check
  (AlgebraicGeometry.ChernClass.Complex.newtonClass_eq_of_representatives :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (π : X ⟶ S) [LocallyOfFiniteType π]
      (classes : AlgebraicGeometry.ChernClass.Theory δ π)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (K L : CochainComplex X.Modules ℤ)
      (hKAbove : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
      (hKBelow : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
      (hKFree : ∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (K.X n))
      (hKRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
      (hLAbove : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove L)
      (hLBelow : AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedBelow L)
      (hLFree : ∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (L.X n))
      (hLRep : IsIsomorphic (DerivedCategory.Q.obj L) E) (p : ℕ),
      AlgebraicGeometry.ChernClass.Complex.newtonClass δ π classes K
          hKAbove hKBelow hKFree p =
        AlgebraicGeometry.ChernClass.Complex.newtonClass δ π classes L
          hLAbove hLBelow hLFree p)
