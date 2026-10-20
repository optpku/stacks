/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.FlatQuasiFinite

variable {U X : Scheme.{u}}

/-- Derived pullback along a flat quasi-finite morphism preserves boundedness of
a bounded complex with coherent cohomology. -/
theorem pullbackObjBounded (h : U ⟶ X) [IsLocallyNoetherian U]
    [IsLocallyNoetherian X] [Flat h] [Scheme.Hom.QuasiFinite h]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (t.bounded : ObjectProperty (DerivedCategory U.Modules))
      ((RingedSpace.modulePullbackDerived h.toShHom).obj
        ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K)) := sorry

/-- Flat quasi-finite pullback of bounded coherent complexes, before recording
coherent cohomology on the target. -/
noncomputable def pullbackInBounded (h : U ⟶ X) [IsLocallyNoetherian U]
    [IsLocallyNoetherian X] [Flat h] [Scheme.Hom.QuasiFinite h] :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
      DerivedCategory.Bounded U.Modules :=
  (t.bounded : ObjectProperty (DerivedCategory U.Modules)).lift
    (ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
      RingedSpace.modulePullbackDerived h.toShHom) (pullbackObjBounded h)

/-- Bounded derived pullback along a flat quasi-finite morphism of locally
Noetherian schemes has coherent cohomology. -/
theorem pullbackMapsTo (h : U ⟶ X) [IsLocallyNoetherian U]
    [IsLocallyNoetherian X] [Flat h] [Scheme.Hom.QuasiFinite h]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent U.ringCatSheaf) :
        ObjectProperty (DerivedCategory.Bounded U.Modules))
      ((pullbackInBounded h).obj K) := sorry

/-- Bounded-coherent derived pullback along a flat quasi-finite morphism of
locally Noetherian schemes. -/
noncomputable def pullback (h : U ⟶ X) [IsLocallyNoetherian U]
    [IsLocallyNoetherian X] [Flat h] [Scheme.Hom.QuasiFinite h] :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf] :=
  (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent U.ringCatSheaf) :
        ObjectProperty (DerivedCategory.Bounded U.Modules)).lift
    (pullbackInBounded h) (pullbackMapsTo h)

/-- Naturality of the identity comparison between bounded-coherent flat
quasi-finite pullback and ambient derived pullback. -/
theorem pullbackAmbientIso_naturality (h : U ⟶ X) [IsLocallyNoetherian U]
    [IsLocallyNoetherian X] [Flat h] [Scheme.Hom.QuasiFinite h]
    {K L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]} (a : K ⟶ L) :
    ((pullback h) ⋙ ambient
        (SheafOfModules.isCoherent U.ringCatSheaf)).map a ≫ 𝟙 _ =
      𝟙 _ ≫ (ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
        RingedSpace.modulePullbackDerived h.toShHom).map a := sorry

/-- Bounded-coherent flat quasi-finite pullback has ordinary derived pullback
as its underlying ambient functor. -/
noncomputable def pullbackAmbientIso (h : U ⟶ X) [IsLocallyNoetherian U]
    [IsLocallyNoetherian X] [Flat h] [Scheme.Hom.QuasiFinite h] :
    pullback h ⋙ ambient (SheafOfModules.isCoherent U.ringCatSheaf) ≅
      ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
        RingedSpace.modulePullbackDerived h.toShHom :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun a ↦ pullbackAmbientIso_naturality h a)

/-- Every component of `pullbackAmbientIso` is the identity on the underlying
derived object. -/
theorem pullbackAmbientIso_hom_app (h : U ⟶ X) [IsLocallyNoetherian U]
    [IsLocallyNoetherian X] [Flat h] [Scheme.Hom.QuasiFinite h]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (pullbackAmbientIso h).hom.app K = 𝟙 _ := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.FlatQuasiFinite
