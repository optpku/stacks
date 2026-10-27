/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap48.Example_48_22_1
public import stacks_project.Chap48.Lemma_48_22_3
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingModule

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ExceptionalInverseImage

/- The four statements use the direct proper QCoh right adjoint and the canonical affine tilde
object. The historical namespace is retained only as a facade. -/

/- Lemma 48.22.4 (1) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.nonzeroCohomology_degreeBounds :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [hA₀ : HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
      [hA₁ : HomotopyCategory.KFlat.TensorDescends (C := ModuleCat.{u} A)]
      [hA₂ : DerivedCategory.KFlat.IsLocalization (C := ModuleCat.{u} A)]
      (HA : @MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) _
        (DerivedCategory.KFlat.monoidalCategory (C := ModuleCat.{u} A)))
      [hX₀ : RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [hX₁ : RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [hX₂ : RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      (HX : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (a : DerivedQCoh (Spec (CommRingCat.of A)) ⥤ DerivedQCoh X)
      (aAdj : DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ)
      (hi : ¬ IsZero (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) i)),
      -(d : ℤ) ≤ i ∧ i ≤ 0)

/- Lemma 48.22.4 (2) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.cohomology_supportDimension_le :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [hA₀ : HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
      [hA₁ : HomotopyCategory.KFlat.TensorDescends (C := ModuleCat.{u} A)]
      [hA₂ : DerivedCategory.KFlat.IsLocalization (C := ModuleCat.{u} A)]
      (HA : @MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) _
        (DerivedCategory.KFlat.monoidalCategory (C := ModuleCat.{u} A)))
      [hX₀ : RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [hX₁ : RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [hX₂ : RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      (HX : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (a : DerivedQCoh (Spec (CommRingCat.of A)) ⥤ DerivedQCoh X)
      (aAdj : DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ),
      topologicalKrullDim (RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) i)) ≤
        if i ≤ 0 then ((-i).toNat : WithBot ℕ∞) else ⊥)

/- Lemma 48.22.4 (3) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.dualizingModule_support_eq_topComponents :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [hA₀ : HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
      [hA₁ : HomotopyCategory.KFlat.TensorDescends (C := ModuleCat.{u} A)]
      [hA₂ : DerivedCategory.KFlat.IsLocalization (C := ModuleCat.{u} A)]
      (HA : @MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) _
        (DerivedCategory.KFlat.monoidalCategory (C := ModuleCat.{u} A)))
      [hX₀ : RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [hX₁ : RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [hX₂ : RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      (HX : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (a : DerivedQCoh (Spec (CommRingCat.of A)) ⥤ DerivedQCoh X)
      (aAdj : DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d),
      RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ))) =
        ⋃ Z : irreducibleComponents X,
          ⋃ (_ : topologicalKrullDim Z = topologicalKrullDim X), (Z : Set X))

/- Lemma 48.22.4 (4) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.dualizingModule_satisfiesSerreConditionSTwo :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [hA₀ : HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
      [hA₁ : HomotopyCategory.KFlat.TensorDescends (C := ModuleCat.{u} A)]
      [hA₂ : DerivedCategory.KFlat.IsLocalization (C := ModuleCat.{u} A)]
      (HA : @MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) _
        (DerivedCategory.KFlat.monoidalCategory (C := ModuleCat.{u} A)))
      [hX₀ : RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [hX₁ : RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [hX₂ : RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      (HX : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (a : DerivedQCoh (Spec (CommRingCat.of A)) ⥤ DerivedQCoh X)
      (aAdj : DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d),
      @Scheme.Modules.satisfiesSerreConditionS X
        (LocallyOfFiniteType.isLocallyNoetherian f)
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ)))
        (AlgebraicGeometry.Scheme.DerivedQCoh.isDualizingModule_of_proper
          HA HX ωA hωA f a aAdj d h_dimension).coherent 2)

end AlgebraicGeometry.Scheme.ExceptionalInverseImage
