/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Zero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Graded.Colimits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ExceptionalInverseImage

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- The canonical `ModuleCat` graded tensor instance is mathematically available, but unfolding
  `TensorDescends` at each theorem binder can make typeclass search revisit its full dependent
  target.  Giving this existing instance a local named route keeps the same genuine tensor
  dependency while making elaboration deterministic. -/
local instance moduleCatHasGoodTensorTensor₂₃ {R : Type u} [CommRing R]
    (G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R)) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ :=
  ModuleCat.gradedHasGoodTensorRight G₁ G₂ G₃

local instance moduleCatHasGoodTensor₁₂Tensor {R : Type u} [CommRing R]
    (G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R)) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ :=
  ModuleCat.gradedHasGoodTensorLeft G₁ G₂ G₃

local instance moduleCatHasTensor₄ObjExt {R : Type u} [CommRing R]
    (G₁ G₂ G₃ G₄ : GradedObject ℤ (ModuleCat R)) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ :=
  ModuleCat.gradedHasTensorFourExt G₁ G₂ G₃ G₄

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-!
The proper-local statements below are formulated for the derived quasicoherent right adjoint.
The all-module `ExceptionalInverseImage` API is deliberately not used: Brown representability
there produces an ambient right adjoint and does not preserve quasicoherence.  The proofs are
therefore retained as explicit geometric Prop debts while their data and tensor structures are
fully exposed in the statements.
-/

/-- Proper duality for the canonical QCoh right adjoint, at the leftmost degree. -/
theorem isDualizingModule_of_proper
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    RingedSpace.ModuleDerived.IsDualizingModule
      ((a.obj ((affineTilde (CommRingCat.of A)).obj ωA)).obj) HX (-(d : ℤ))
      (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ))) := sorry

/-- Proper duality bounds the nonzero cohomology degrees of the canonical QCoh value. -/
theorem nonzeroCohomology_degreeBounds_of_proper
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
      ((a.obj ((affineTilde (CommRingCat.of A)).obj ωA)).obj) i)) :
    -(d : ℤ) ≤ i ∧ i ≤ 0 := sorry

/-- Proper duality bounds the support dimension in every cohomological degree. -/
theorem cohomology_supportDimension_le_of_proper
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ) :
    topologicalKrullDim
        (RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
          ((a.obj ((affineTilde (CommRingCat.of A)).obj ωA)).obj) i)) ≤
      if i ≤ 0 then ((-i).toNat : WithBot ℕ∞) else ⊥ := sorry

/-- The leftmost cohomology is supported on the maximal-dimensional components. -/
theorem dualizingModule_support_eq_topComponents_of_proper
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ))) =
      ⋃ Z : irreducibleComponents X,
        ⋃ (_ : topologicalKrullDim Z = topologicalKrullDim X), (Z : Set X) := sorry

/-- The leftmost proper-duality module satisfies Serre's condition `(S₂)`. -/
theorem dualizingModule_satisfiesSerreConditionSTwo_of_proper
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    @Scheme.Modules.satisfiesSerreConditionS X
      (LocallyOfFiniteType.isLocallyNoetherian f)
      (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ)))
      (isDualizingModule_of_proper HA HX ωA hωA f a aAdj d
        h_dimension).coherent 2 := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme

/-- Historical name for the direct QCoh proper-duality theorem. -/
theorem isDualizingModule_of_proper
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    RingedSpace.ModuleDerived.IsDualizingModule
      ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) HX (-(d : ℤ))
      (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ))) := by
  exact DerivedQCoh.isDualizingModule_of_proper HA HX ωA hωA f a aAdj d
    h_dimension

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.ExceptionalInverseImage

/-- Historical alias for the direct QCoh proper-duality degree bound. -/
theorem nonzeroCohomology_degreeBounds
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
      ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) i)) :
    -(d : ℤ) ≤ i ∧ i ≤ 0 := by
  exact DerivedQCoh.nonzeroCohomology_degreeBounds_of_proper HA HX ωA hωA f a aAdj d
    h_dimension i hi

/-- Historical alias for the direct QCoh support-dimension bound. -/
theorem cohomology_supportDimension_le
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ) :
    topologicalKrullDim (RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
      ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) i)) ≤
      if i ≤ 0 then ((-i).toNat : WithBot ℕ∞) else ⊥ := by
  exact DerivedQCoh.cohomology_supportDimension_le_of_proper HA HX ωA hωA f a aAdj d
    h_dimension i

/-- Historical alias for the direct maximal-component support theorem. -/
theorem dualizingModule_support_eq_topComponents
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ))) =
      ⋃ Z : irreducibleComponents X,
        ⋃ (_ : topologicalKrullDim Z = topologicalKrullDim X), (Z : Set X) := by
  exact DerivedQCoh.dualizingModule_support_eq_topComponents_of_proper HA HX ωA hωA f a aAdj d
    h_dimension

/-- Historical alias for the direct proper-duality `S₂` theorem. -/
theorem dualizingModule_satisfiesSerreConditionSTwo
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}}
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
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    @Scheme.Modules.satisfiesSerreConditionS X
      (LocallyOfFiniteType.isLocallyNoetherian f)
      (RingedSpace.ModuleDerived.cohomologySheaf
        ((a.obj ((DerivedQCoh.affineTilde (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ)))
      (AlgebraicGeometry.Scheme.DerivedQCoh.isDualizingModule_of_proper HA HX ωA hωA f a aAdj d
        h_dimension).coherent 2 := by
  exact DerivedQCoh.dualizingModule_satisfiesSerreConditionSTwo_of_proper HA HX ωA hωA f a aAdj d
    h_dimension

end AlgebraicGeometry.Scheme.ExceptionalInverseImage
