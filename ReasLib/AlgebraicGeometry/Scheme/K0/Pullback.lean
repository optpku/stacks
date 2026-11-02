/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.CategoryTheory.Pretriangulated.K0.Additivity

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0

variable {X Y Z : Scheme.{u}}

/-- Canonical derived pullback values kill the triangulated Grothendieck relations. -/
theorem relations_le_ker_pullback (f : X ⟶ Y) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun K ↦
        TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K)).ker := by
  letI := RingedSpace.modulePullbackDerived.commShift f.toShHom
  letI : (RingedSpace.modulePullbackDerived f.toShHom).IsTriangulated :=
    RingedSpace.modulePullbackDerived.isTriangulated f.toShHom
  letI : (RingedSpace.modulePullbackPerfect f.toShHom).CommShift ℤ := by
    unfold RingedSpace.modulePullbackPerfect ObjectProperty.FullSubcategory.restrict
    infer_instance
  letI : (RingedSpace.modulePullbackPerfect f.toShHom).IsTriangulated := by
    unfold RingedSpace.modulePullbackPerfect ObjectProperty.FullSubcategory.restrict
    exact ObjectProperty.isTriangulated_lift _ _ _
  apply (AddSubgroup.closure_le _).mpr
  rintro _ ⟨T, rfl⟩
  change (FreeAbelianGroup.lift fun K ↦
    TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K))
      (TriangulatedK0.relation _ T.val) = 0
  simp only [TriangulatedK0.relation, map_sub, FreeAbelianGroup.lift_apply_of]
  have hrel : TriangulatedK0.relation _
      ((RingedSpace.modulePullbackPerfect f.toShHom).mapTriangle.obj T.val) ∈
        TriangulatedK0.relations
          (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :=
    AddSubgroup.subset_closure ⟨⟨_,
      (RingedSpace.modulePullbackPerfect f.toShHom).map_distinguished _ T.property⟩, rfl⟩
  have hzero := (QuotientAddGroup.eq_zero_iff _).mpr hrel
  change (QuotientAddGroup.mk' _)
    (TriangulatedK0.relation _
      ((RingedSpace.modulePullbackPerfect f.toShHom).mapTriangle.obj T.val)) = 0 at hzero
  set_option backward.isDefEq.respectTransparency false in
    simpa only [TriangulatedK0.relation, Functor.mapTriangle_obj,
      Pretriangulated.Triangle.mk, TriangulatedK0.of,
      map_sub, sub_eq_add_neg, map_add, map_neg] using hzero

/-- The additive pullback induced by canonical derived pullback on perfect complexes. -/
noncomputable def pullbackAdd (f : X ⟶ Y) : K0 Y →+ K0 X :=
  TriangulatedK0.lift
    (fun K ↦ TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K))
    (relations_le_ker_pullback f)

/-- The additive pullback sends a perfect generator to its derived pullback. -/
theorem pullbackAdd_of (f : X ⟶ Y)
    (K : RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) :
    pullbackAdd f (TriangulatedK0.of K) =
      TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K) := by
  change (FreeAbelianGroup.lift fun L ↦
    TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj L))
      (FreeAbelianGroup.of K) = _
  exact FreeAbelianGroup.lift_apply_of _ K

/-- The additive pullback preserves the multiplicative unit in perfect-complex `K₀`. -/
theorem pullbackAdd_map_one (f : X ⟶ Y) :
    pullbackAdd f (1 : K0 Y) = 1 := sorry

/-- The additive pullback preserves multiplication in perfect-complex `K₀`. -/
theorem pullbackAdd_map_mul (f : X ⟶ Y) (a b : K0 Y) :
    pullbackAdd f (a * b) = pullbackAdd f a * pullbackAdd f b := sorry

/-- Pullback on perfect-complex Grothendieck groups. -/
noncomputable def pullback (f : X ⟶ Y) : K0 Y →+* K0 X :=
  { pullbackAdd f with
    map_one' := pullbackAdd_map_one f
    map_mul' := pullbackAdd_map_mul f }

/-- Pullback sends the class of a perfect complex to the class of its derived pullback. -/
theorem pullback_of (f : X ⟶ Y)
    (K : RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) :
    pullback f (TriangulatedK0.of K) =
      TriangulatedK0.of ((RingedSpace.modulePullbackPerfect f.toShHom).obj K) := by
  exact pullbackAdd_of f K

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along the identity morphism is the identity on perfect-complex `K₀`. -/
theorem pullback_id (X : Scheme.{u}) :
    pullback (𝟙 X) = RingHom.id (K0 X) := by
  let Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
      RingedSpace.ModuleDerived X.toRingedSpace := DerivedCategory.Qh (C := X.toRingedSpace.Modules)
  let eId : (𝟭 X.Modules).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory X.Modules (ComplexShape.up ℤ)) :=
    Quotient.natIsoLift _
      (Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ))
        (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)))
  let eSource : RingedSpace.modulePullbackToDerived (𝟙 X.toRingedSpace) ≅ Qh :=
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (RingedSpace.Hom.pullbackIdIso X.toRingedSpace) ≪≫ eId)
      Qh ≪≫ Functor.leftUnitor Qh
  let e : Qh ⋙ 𝟭 (RingedSpace.ModuleDerived X.toRingedSpace) ≅
      RingedSpace.modulePullbackToDerived (𝟙 X.toRingedSpace) :=
    Functor.rightUnitor Qh ≪≫ eSource.symm
  letI : Qh.IsLocalization (RingedSpace.ModuleQis X.toRingedSpace) := by
    dsimp only [Qh, RingedSpace.ModuleQis]
    infer_instance
  letI : ((Functor.whiskeringLeft _ _ (RingedSpace.ModuleDerived X.toRingedSpace)).obj Qh).Full :=
    Localization.full_whiskeringLeft Qh (RingedSpace.ModuleQis X.toRingedSpace) _
  letI : ((Functor.whiskeringLeft _ _ (RingedSpace.ModuleDerived X.toRingedSpace)).obj Qh).Faithful :=
    Localization.faithful_whiskeringLeft Qh (RingedSpace.ModuleQis X.toRingedSpace) _
  letI : (𝟭 (RingedSpace.ModuleDerived X.toRingedSpace)).IsRightKanExtension
      (𝟙 (Qh ⋙ 𝟭 (RingedSpace.ModuleDerived X.toRingedSpace))) :=
    ⟨⟨CostructuredArrow.mkIdTerminal⟩⟩
  letI : (𝟭 (RingedSpace.ModuleDerived X.toRingedSpace)).IsLeftDerivedFunctor
      e.hom (RingedSpace.ModuleQis X.toRingedSpace) := by
    constructor
    exact (Functor.isRightKanExtension_iff_of_iso₂ (𝟙 _) e.hom e (Iso.refl _)
      (by simp)).mp inferInstance
  let eDerived : RingedSpace.modulePullbackDerived (𝟙 X.toRingedSpace) ≅
      𝟭 (RingedSpace.ModuleDerived X.toRingedSpace) :=
    Functor.leftDerivedNatIso
      (RingedSpace.modulePullbackDerived (𝟙 X.toRingedSpace))
      (𝟭 (RingedSpace.ModuleDerived X.toRingedSpace))
      ((RingedSpace.modulePullbackToDerived (𝟙 X.toRingedSpace)).totalLeftDerivedCounit
        Qh (RingedSpace.ModuleQis X.toRingedSpace))
      e.hom (RingedSpace.ModuleQis X.toRingedSpace) (Iso.refl _)
  apply RingHom.coe_addMonoidHom_injective
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro K
  change pullback (𝟙 X) (TriangulatedK0.of K) = TriangulatedK0.of K
  rw [pullback_of]
  apply TriangulatedK0.of_iso
  exact (RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace)).isoMk
    (eDerived.app K.obj)

/-- Pullback is contravariantly functorial under composition. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  apply RingHom.coe_addMonoidHom_injective
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro K
  change pullback (f ≫ g) (TriangulatedK0.of K) =
    pullback f (pullback g (TriangulatedK0.of K))
  rw [pullback_of, pullback_of, pullback_of]
  apply TriangulatedK0.of_iso
  exact (RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace)).isoMk
    ((RingedSpace.modulePullbackDerived.canonicalCompIso f.toShHom g.toShHom).symm.app K.obj)

end AlgebraicGeometry.Scheme.K0
