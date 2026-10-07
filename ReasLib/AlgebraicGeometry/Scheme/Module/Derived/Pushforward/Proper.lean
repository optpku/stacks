module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open DerivedCategory.Bounded.CohomologyIn
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X Y : Scheme.{v}} (f : X ⟶ Y)
variable [IsNoetherian X] [IsNoetherian Y] [IsProper f]

/-- Ambient derived pushforward along a proper morphism of Noetherian schemes sends a bounded
coherent complex to a bounded derived object. -/
theorem properPushforward_obj_bounded
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (t.bounded : ObjectProperty (DerivedCategory Y.Modules))
      ((ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
        RingedSpace.moduleDerivedPushforward f.toShHom).obj K) := by
  -- Local instance justification (proof-local temporary data): support facts are needed only while applying the bounded proper-pushforward theorem.
  letI h_support : ∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf
        ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K) i) := by
    intro i
    let ℱ := RingedSpace.ModuleDerived.cohomologySheaf
      ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K) i
    have hcoh : ℱ.IsCoherent :=
      DerivedCategory.Bounded.CohomologyIn.homology_mem
        (SheafOfModules.isCoherent X.ringCatSheaf) K i
    -- Local instance justification (proof-local temporary data): derive finiteness properties from the coherent cohomology fact for this support construction.
    letI : ℱ.IsCoherent := hcoh
    -- Local instance justification (proof-local temporary data): expose the quasi-coherence component only for constructing the support witness.
    letI : ℱ.IsQuasicoherent :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType ℱ).mp hcoh |>.1
    -- Local instance justification (proof-local temporary data): expose the finite-type component only for constructing the support witness.
    letI : ℱ.IsFiniteType :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType ℱ).mp hcoh |>.2
    exact ⟨Scheme.Modules.isClosed_moduleSupport ℱ, by infer_instance⟩
  exact (pushforwardBoundedCoherentOfProperSupport f
    ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K)
    K.property K.obj.property).2

/-- Proper derived pushforward restricted to bounded objects, before recording coherence of its
cohomology. -/
noncomputable def properPushforwardInBounded :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
      DerivedCategory.Bounded Y.Modules :=
  (t.bounded : ObjectProperty (DerivedCategory Y.Modules)).lift
    (ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
      RingedSpace.moduleDerivedPushforward f.toShHom)
    (properPushforward_obj_bounded f)

/-- The bounded proper pushforward of a bounded coherent complex has coherent cohomology. -/
theorem properPushforwardInBounded_obj_coherent
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent Y.ringCatSheaf) :
        ObjectProperty (DerivedCategory.Bounded Y.Modules))
      ((properPushforwardInBounded f).obj K) := by
  -- Local instance justification (proof-local temporary data): support facts are needed only while applying the bounded proper-pushforward theorem.
  letI h_support : ∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf
        ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K) i) := by
    intro i
    let ℱ := RingedSpace.ModuleDerived.cohomologySheaf
      ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K) i
    have hcoh : ℱ.IsCoherent :=
      DerivedCategory.Bounded.CohomologyIn.homology_mem
        (SheafOfModules.isCoherent X.ringCatSheaf) K i
    -- Local instance justification (proof-local temporary data): derive finiteness properties from the coherent cohomology fact for this support construction.
    letI : ℱ.IsCoherent := hcoh
    -- Local instance justification (proof-local temporary data): expose the quasi-coherence component only for constructing the support witness.
    letI : ℱ.IsQuasicoherent :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType ℱ).mp hcoh |>.1
    -- Local instance justification (proof-local temporary data): expose the finite-type component only for constructing the support witness.
    letI : ℱ.IsFiniteType :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType ℱ).mp hcoh |>.2
    exact ⟨Scheme.Modules.isClosed_moduleSupport ℱ, by infer_instance⟩
  exact (pushforwardBoundedCoherentOfProperSupport f
    ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K)
    K.property K.obj.property).1

/-- Proper derived pushforward on bounded complexes with coherent cohomology. -/
noncomputable def properPushforward :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
      Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf] :=
  (DerivedCategory.Bounded.cohomologyIn
    (SheafOfModules.isCoherent Y.ringCatSheaf) :
      ObjectProperty (DerivedCategory.Bounded Y.Modules)).lift
    (properPushforwardInBounded f)
    (properPushforwardInBounded_obj_coherent f)

namespace properPushforward

/-- Forgetting boundedness and coherent cohomology from proper pushforward recovers the ambient
derived pushforward. -/
noncomputable def ambientIso :
    properPushforward f ⋙ ambient (SheafOfModules.isCoherent Y.ringCatSheaf) ≅
      ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
        RingedSpace.moduleDerivedPushforward f.toShHom :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      ((DerivedCategory.Bounded.cohomologyIn
        (SheafOfModules.isCoherent Y.ringCatSheaf) :
          ObjectProperty (DerivedCategory.Bounded Y.Modules)).liftCompιIso
        (properPushforwardInBounded f)
        (properPushforwardInBounded_obj_coherent f))
      DerivedCategory.Bounded.ι ≪≫
    (t.bounded : ObjectProperty (DerivedCategory Y.Modules)).liftCompιIso
      (ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
        RingedSpace.moduleDerivedPushforward f.toShHom)
      (properPushforward_obj_bounded f)

/-- The ambient object underlying proper pushforward is the ambient derived pushforward. -/
theorem obj_obj (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (ambient (SheafOfModules.isCoherent Y.ringCatSheaf)).obj
        ((properPushforward f).obj K) =
      (RingedSpace.moduleDerivedPushforward f.toShHom).obj
        ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K) := sorry

/-- The ambient morphism underlying proper pushforward is the ambient derived pushforward map. -/
theorem map_hom {K L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]} (g : K ⟶ L) :
    (ambient (SheafOfModules.isCoherent Y.ringCatSheaf)).map
        ((properPushforward f).map g) =
      (RingedSpace.moduleDerivedPushforward f.toShHom).map
        ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).map g) := sorry

end properPushforward

end AlgebraicGeometry.Scheme.ModuleDerived
