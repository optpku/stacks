/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.DivisorComplexChart

/-- Scalar extension of a bounded affine-chart model is bounded. -/
theorem pullback_bounded {X Y : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (h : Y ⟶ X)
    (C : DivisorComplexChart D M) (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    CochainComplex.bounded (ModuleCat Γ(Y, V))
      (((ModuleCat.extendScalars (h.appLE C.U V hV).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.model) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := C.bounded
  letI := ha
  letI := hb
  exact ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩

/-- Scalar extension of an affine-chart model is termwise finite free. -/
theorem pullback_finiteFree {X Y : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (h : Y ⟶ X)
    (C : DivisorComplexChart D M) (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    (((ModuleCat.extendScalars (h.appLE C.U V hV).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C.model).IsTermwiseFiniteFree := by
  refine ⟨fun i ↦ ?_⟩
  letI := (@HomologicalComplex.IsTermwiseFiniteFree.out _ _ _ _ C.model C.finiteFree i).1
  letI := (@HomologicalComplex.IsTermwiseFiniteFree.out _ _ _ _ C.model C.finiteFree i).2
  exact ⟨ModuleCat.ExtendScalars.free _ _, ModuleCat.ExtendScalars.finite _ _⟩

/-- The image of a chart equation is regular when the divisor pullback is defined. -/
theorem pullback_regular {X Y : Scheme.{u}} {D : X.IdealSheafData}
    [IsEffectiveCartierDivisor D.subschemeι]
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (C : DivisorComplexChart D M)
    (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    (h.appLE C.U V hV).hom C.generator ∈ nonZeroDivisors Γ(Y, V) := sorry

/-- The image of a chart equation generates the pulled-back divisor ideal. -/
theorem pullback_ideal_eq {X Y : Scheme.{u}} {D : X.IdealSheafData}
    [IsEffectiveCartierDivisor D.subschemeι]
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (C : DivisorComplexChart D M)
    (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    (D.comap h).ideal V = Ideal.span {(h.appLE C.U V hV).hom C.generator} := sorry

/-- The scalar-extended chart model represents derived sections of the ambient derived
pullback on the chosen affine open. -/
theorem pullback_represents {X Y : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace}
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    (C : DivisorComplexChart D M) (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (h.appLE C.U V hV).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C.model))
      ((RingedSpace.moduleDerivedSectionsAtOpen Y.toRingedSpace V).obj
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M)) := sorry

/-- Restriction to an affine open in an inverse image gives the divisor-complex chart whose
equation and model are obtained by scalar extension. -/
noncomputable def pullback {X Y : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (C : DivisorComplexChart D M)
    (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    DivisorComplexChart (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) where
  U := V
  generator := (h.appLE C.U V hV).hom C.generator
  model := ((ModuleCat.extendScalars (h.appLE C.U V hV).hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj C.model
  bounded := pullback_bounded h C V hV
  finiteFree := pullback_finiteFree h C V hV
  regular := pullback_regular h hpull C V hV
  ideal_eq := pullback_ideal_eq h hpull C V hV
  represents := pullback_represents hM h C V hV

/-- The pulled-back chart has the prescribed affine open. -/
theorem pullback_U {X Y : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (C : DivisorComplexChart D M)
    (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    (C.pullback D M hM h hpull V hV).U = V := rfl

/-- The pulled-back chart equation is the image of the original equation. -/
theorem pullback_generator {X Y : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (C : DivisorComplexChart D M)
    (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    (C.pullback D M hM h hpull V hV).generator =
      (h.appLE C.U V hV).hom C.generator := rfl

/-- The pulled-back chart model is degreewise scalar extension of the original model. -/
theorem pullback_model {X Y : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (C : DivisorComplexChart D M)
    (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) :
    (C.pullback D M hM h hpull V hV).model =
      ((ModuleCat.extendScalars (h.appLE C.U V hV).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.model := rfl

/-- Each degreewise determinantal ideal of a scalar-extended chart is the extension of the
corresponding ideal of the original chart. -/
theorem ideal_pullback {X Y : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (C : DivisorComplexChart D M)
    (V : Y.affineOpens) (hV : V ≤ h ⁻¹ᵁ C.U) (i : ℤ) :
    Ideal.map (h.appLE C.U V hV).hom (C.ideal i) =
      (C.pullback D M hM h hpull V hV).ideal i := by
  letI := (h.appLE C.U V hV).hom.toAlgebra
  letI := C.finiteFree
  exact (CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal_baseChange
    (B := Γ(Y, V)) C.generator C.model i).symm

end AlgebraicGeometry.Scheme.DivisorComplexChart

namespace AlgebraicGeometry.Scheme.IsGoodTriple

/-- Goodness of a perfect divisor-complex triple is preserved by derived pullback along a
morphism for which the divisor pullback is defined. -/
theorem pullback {X Y : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    (hpull : D.pullbackDefined h) (hgood : IsGoodTriple D M) :
    IsGoodTriple (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) := by
  intro y
  have hy : h ((D.comap h).subschemeι y) ∈ (D.support : Set X) := by
    change (D.comap h).subschemeι y ∈ D.support.preimage h.continuous
    rw [← IdealSheafData.support_comap]
    change (D.comap h).subschemeι y ∈ ((D.comap h).support : Set Y)
    rw [← IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  rw [← IdealSheafData.range_subschemeι] at hy
  obtain ⟨x, hx⟩ := hy
  obtain ⟨C, hxU, hprincipal⟩ := hgood x
  have hyU : (D.comap h).subschemeι y ∈ h ⁻¹ᵁ C.U := by
    change h ((D.comap h).subschemeι y) ∈ (C.U : X.Opens)
    rwa [← hx]
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (h ⁻¹ᵁ C.U).2
  refine ⟨C.pullback D M hM h hpull ⟨V, hV⟩ hVU, hyV, fun i ↦ ?_⟩
  rw [← DivisorComplexChart.ideal_pullback]
  letI := hprincipal i
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (C.ideal i)
  refine ⟨(h.appLE C.U V hVU).hom a, ?_⟩
  change Ideal.map _ (C.ideal i) = Ideal.span {_}
  rw [ha, Ideal.map_span, Set.image_singleton]

end AlgebraicGeometry.Scheme.IsGoodTriple
