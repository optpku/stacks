/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.PullbackSections
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DualizingModule
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
open RingedSpace.Module.Derived

noncomputable section

universe u

namespace IsRationalSingularity

/-- The degree-minus-two derived global-sections functor over `Spec A`, with scalars
transported back to `A`. -/
noncomputable abbrev dualizingGlobalSectionsFunctor (A : Type u) [CommRing A] :
    RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤ ModuleCat.{u} A :=
  GlobalSections.functor
      (Spec (CommRingCat.of A)).toRingedSpace ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat (Scheme.globalSectionsRing (Spec (CommRingCat.of A)))) (-2 : ℤ) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The normalized dualizing trace from global sections on `X` to the base dualizing module. -/
noncomputable def dualizingTrace
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : Scheme.Hom.globalSectionsMod f ωX ≅
      (dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA) :
    Scheme.Hom.globalSectionsMod f ωX ⟶ ωA :=
  sourceComparison.hom ≫
    (dualizingGlobalSectionsFunctor A).map
      ((RingedSpace.moduleDerivedPushforward f.toShHom).map e.inv ≫
        aAdjunction.counit.app ωS) ≫
    targetComparison.hom

/-- The normalized trace is an isomorphism for a rational singularity. -/
theorem dualizingTrace_isIso
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : Scheme.Hom.globalSectionsMod f ωX ≅
      (dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA) :
    IsIso (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
      ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) := sorry

/-- The adjunction mate of an explicitly supplied inverse to the normalized trace.
The two inverse laws characterize the Stacks map uniquely.  The inverse is input data:
this definition does not extract it from the admitted theorem `dualizingTrace_isIso`.
See `canonicalDualizingPullbackMap_existsUnique` for the source-facing existence statement. -/
noncomputable def canonicalDualizingPullbackMap
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : Scheme.Hom.globalSectionsMod f ωX ≅
      (dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA)
    (traceInverse : ωA ⟶ Scheme.Hom.globalSectionsMod f ωX)
    (traceInverse_hom_id : traceInverse ≫
      (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) = 𝟙 ωA)
    (hom_traceInverse_id :
      (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) ≫ traceInverse =
        𝟙 (Scheme.Hom.globalSectionsMod f ωX)) :
    (Scheme.Modules.pullback f).obj (AlgebraicGeometry.tilde ωA) ⟶ ωX :=
  (Scheme.Modules.pullbackTildeHomEquiv f ωA ωX).symm traceInverse

/-- The adjunction mate of the constructed map is exactly the supplied inverse trace. -/
theorem canonicalDualizingPullbackMap_spec
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : Scheme.Hom.globalSectionsMod f ωX ≅
      (dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA)
    (traceInverse : ωA ⟶ Scheme.Hom.globalSectionsMod f ωX)
    (traceInverse_hom_id : traceInverse ≫
      (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) = 𝟙 ωA)
    (hom_traceInverse_id :
      (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) ≫ traceInverse =
        𝟙 (Scheme.Hom.globalSectionsMod f ωX)) :
    (Scheme.Modules.pullbackTildeHomEquiv f ωA ωX)
      (canonicalDualizingPullbackMap A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA
        HS ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison
        traceInverse traceInverse_hom_id hom_traceInverse_id) = traceInverse :=
  (Scheme.Modules.pullbackTildeHomEquiv f ωA ωX).apply_symm_apply traceInverse

/-- Stacks, Tag 0BBU: there is a unique pullback map whose adjunction mate is a
two-sided inverse of the normalized trace.  This is a proposition, so the still-admitted
trace-isomorphism theorem is not used to manufacture data for a definition. -/
theorem canonicalDualizingPullbackMap_existsUnique
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : Scheme.Hom.globalSectionsMod f ωX ≅
      (dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA) :
    ∃! φ : (Scheme.Modules.pullback f).obj (AlgebraicGeometry.tilde ωA) ⟶ ωX,
      (Scheme.Modules.pullbackTildeHomEquiv f ωA ωX) φ ≫
          (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
            ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) = 𝟙 ωA ∧
        (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
          ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) ≫
          (Scheme.Modules.pullbackTildeHomEquiv f ωA ωX) φ =
            𝟙 (Scheme.Hom.globalSectionsMod f ωX) := by
  let τ := dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison
  let E := Scheme.Modules.pullbackTildeHomEquiv f ωA ωX
  letI : IsIso τ := dualizingTrace_isIso A f h_normal h_locallyNoetherian ωX hωX HA
    ωA hωA HS ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison
  change ∃! φ, E φ ≫ τ = 𝟙 ωA ∧ τ ≫ E φ = 𝟙 _
  refine ⟨E.symm (inv τ), ?_, ?_⟩
  · simp only [Equiv.apply_symm_apply]
    exact ⟨IsIso.inv_hom_id τ, IsIso.hom_inv_id τ⟩
  · intro φ hφ
    apply E.injective
    rw [Equiv.apply_symm_apply]
    calc
      E φ = E φ ≫ (τ ≫ inv τ) := by rw [IsIso.hom_inv_id, Category.comp_id]
      _ = (E φ ≫ τ) ≫ inv τ := (Category.assoc _ _ _).symm
      _ = inv τ := by rw [hφ.1, Category.id_comp]

end IsRationalSingularity
