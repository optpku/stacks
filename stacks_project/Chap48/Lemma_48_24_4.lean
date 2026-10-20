/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Gorenstein
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.KFlat
open DerivedCategory.DerivedTensor.Right.Monoidal

universe u

/- Lemma 48.24.4 (1): A locally Noetherian scheme carrying a dualizing complex is
Gorenstein exactly when that complex is tensor-invertible in `D(𝒪_X)`. -/
@[stacks 0BFQ] #check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.gorenstein_iff_isInvertibleObject :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      Scheme.Gorenstein X ↔ MonoidalCategory.isInvertibleObject ω)

/- Lemma 48.24.4 (2): The local ring at `x` is Gorenstein exactly when the derived
stalk of a dualizing complex at `x` is tensor-invertible. -/
@[stacks 0BFQ] #check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.stalk_gorenstein_iff_isInvertibleObject :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω) (x : X)
      [MonoidalCategory (DerivedCategory (ModuleCat (X.presheaf.stalk x)))]
      (T : @Model (ModuleCat (X.presheaf.stalk x)) _ _ _ _ _ _ _),
      IsGorensteinLocalRing (X.presheaf.stalk x) ↔
        MonoidalCategory.isInvertibleObject (Stalk.obj ω x))

/- Lemma 48.24.4 (3): The locus where the local rings of a locally Noetherian scheme
with a dualizing complex are Gorenstein is open. -/
@[stacks 0BFQ] #check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.isOpen_gorensteinLocus :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      IsOpen (Scheme.gorensteinLocus X))

/- Lemma 48.24.4 (4): The open subscheme on the Gorenstein locus is Gorenstein. -/
@[stacks 0BFQ] #check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.gorensteinOpen_isGorenstein :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      Scheme.Gorenstein hω.gorensteinOpen.toScheme)

/- Lemma 48.24.4 (5): On a Gorenstein scheme, a dualizing complex exists exactly when
the structure sheaf in degree zero is dualizing. -/
@[stacks 0BFQ] #check
  (AlgebraicGeometry.Scheme.Gorenstein.exists_iff_structureSheaf :
    ∀ {X : Scheme.{u}} [Scheme.Gorenstein X],
      (∃ K : RingedSpace.ModuleDerived X.toRingedSpace,
        Scheme.IsDualizingComplex K) ↔
        Scheme.IsDualizingComplex (Scheme.DerivedQCoh.structureSheaf X).obj)

#check (AlgebraicGeometry.Scheme.gorensteinLocus : ∀ (X : Scheme.{u}), Set X)
#check (AlgebraicGeometry.Scheme.mem_gorensteinLocus :
  ∀ (X : Scheme.{u}) (x : X),
    x ∈ X.gorensteinLocus ↔ IsGorensteinLocalRing (X.presheaf.stalk x))
#check (AlgebraicGeometry.Scheme.IsDualizingComplex.gorensteinOpen :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace}
    (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω), X.Opens)
#check (AlgebraicGeometry.Scheme.IsDualizingComplex.coe_gorensteinOpen :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace}
    (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
    (hω.gorensteinOpen : Set X) = Scheme.gorensteinLocus X)
