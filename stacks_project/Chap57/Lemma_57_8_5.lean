/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai.BoundedCoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.5 (1) -/
@[stacks 0FYU] #check (AlgebraicGeometry.Scheme.FourierMukai.mapsBoundedCoherent_of_finiteTorDimension :
    {S X Y : Scheme.{u}} → (f : X ⟶ S) → (g : Y ⟶ S) →
    [DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules
        (RingedSpace.Hom.inverseImageBase (Limits.pullback.fst f g).toShHom))] →
    [IsNoetherian S] → [Scheme.Hom.FiniteType f] → [Scheme.Hom.FiniteType g] →
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) →
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K →
    (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K →
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i)] →
    RingedSpace.HasFiniteTorDimension
      ((RingedSpace.ModuleDerived.relativeRestriction
        (Limits.pullback.fst f g).toShHom).obj K) →
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K))

/- Lemma 57.8.5 (2) -/
@[stacks 0FYU] #check (AlgebraicGeometry.Scheme.FourierMukai.mapsBoundedCoherent_of_flatCoherentRepresentative :
    {S X Y : Scheme.{u}} → (f : X ⟶ S) → (g : Y ⟶ S) →
    [IsNoetherian S] → [Scheme.Hom.FiniteType f] → [Scheme.Hom.FiniteType g] →
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) →
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K →
    (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K →
    (𝒦 : CochainComplex (Limits.pullback f g).toRingedSpace.Modules ℤ) →
    (DerivedCategory.Q.obj 𝒦 ≅ K) →
    CochainComplex.bounded (Limits.pullback f g).toRingedSpace.Modules 𝒦 →
    [∀ i : ℤ, (𝒦.X i).IsCoherent] →
    [∀ i : ℤ, SheafOfModules.IsFlatOver
      (𝒦.X i) (Limits.pullback.fst f g).toShHom] →
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (𝒦.X i)] →
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K))

/- Lemma 57.8.5 (3) -/
@[stacks 0FYU] #check (AlgebraicGeometry.Scheme.FourierMukai.mapsBoundedCoherent_of_regular :
    {S X Y : Scheme.{u}} → (f : X ⟶ S) → (g : Y ⟶ S) →
    [IsNoetherian S] → [Scheme.Hom.FiniteType f] → [Scheme.Hom.FiniteType g] →
    [Scheme.Regular X] →
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) →
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K →
    (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K →
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i)] →
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K))

/- Lemma 57.8.5 (4) -/
@[stacks 0FYU] #check (AlgebraicGeometry.Scheme.FourierMukai.mapsBoundedCoherent_of_perfect_of_flat :
    {S X Y : Scheme.{u}} → (f : X ⟶ S) → (g : Y ⟶ S) →
    [IsNoetherian S] → [Scheme.Hom.FiniteType f] → [Scheme.Hom.FiniteType g] → [Flat g] →
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) →
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K →
    (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K →
    RingedSpace.ModuleDerived.IsPerfect K →
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i)] →
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K))

/- Lemma 57.8.5 (5) -/
@[stacks 0FYU] #check (AlgebraicGeometry.Scheme.FourierMukai.cohomologySheaf_hasProperSupportOver_of_isProper :
    {S X Y : Scheme.{u}} → (f : X ⟶ S) → (g : Y ⟶ S) →
    [IsNoetherian S] → [Scheme.Hom.FiniteType f] → [Scheme.Hom.FiniteType g] → [IsProper f] →
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) →
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K →
    (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K →
    ∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i))

/- Lemma 57.8.5 (6) -/
@[stacks 0FYU] #check (AlgebraicGeometry.Scheme.FourierMukai.representativeTerm_hasProperSupportOver_of_isProper :
    {S X Y : Scheme.{u}} → (f : X ⟶ S) → (g : Y ⟶ S) →
    [IsNoetherian S] → [Scheme.Hom.FiniteType f] → [Scheme.Hom.FiniteType g] → [IsProper f] →
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) →
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K →
    (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K →
    (𝒦 : CochainComplex (Limits.pullback f g).toRingedSpace.Modules ℤ) →
    (DerivedCategory.Q.obj 𝒦 ≅ K) →
    CochainComplex.bounded (Limits.pullback f g).toRingedSpace.Modules 𝒦 →
    [∀ i : ℤ, (𝒦.X i).IsCoherent] →
    [∀ i : ℤ, SheafOfModules.IsFlatOver
      (𝒦.X i) (Limits.pullback.fst f g).toShHom] →
    ∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (𝒦.X i))

end AlgebraicGeometry.Scheme.FourierMukai
