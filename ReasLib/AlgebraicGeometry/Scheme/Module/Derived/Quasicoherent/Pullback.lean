/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction

/-!
# Pullback of Derived Modules with Quasicoherent Cohomology

This module defines derived pullback along arbitrary morphisms of schemes on the unbounded
derived categories of modules with quasicoherent cohomology. It also defines exact pullback
along an open immersion on the unbounded, bounded-below, bounded-above, and bounded categories.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

namespace pullback

/-- Derived pullback along a morphism of schemes preserves quasi-coherent cohomology. -/
theorem mapsTo {X Y : Scheme.{u}} (f : Y ⟶ X) :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).inverseImage
          (RingedSpace.modulePullbackDerived f.toLRSHom.toShHom) := sorry

end pullback

/-- Derived pullback along a morphism of schemes, restricted to derived modules with
quasi-coherent cohomology. -/
noncomputable def pullback {X Y : Scheme.{u}} (f : Y ⟶ X) :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) :=
  (DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).lift
      ((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          RingedSpace.modulePullbackDerived f.toLRSHom.toShHom)
      (fun E ↦ pullback.mapsTo f E.obj E.property)

/-- Forgetting the quasi-coherent lift of derived pullback recovers the ambient derived
pullback functor. -/
noncomputable def pullback.inclusionIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    pullback f ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).ι ≅
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          RingedSpace.modulePullbackDerived f.toLRSHom.toShHom :=
  (DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).liftCompιIso
      ((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          RingedSpace.modulePullbackDerived f.toLRSHom.toShHom)
      (fun E ↦ pullback.mapsTo f E.obj E.property)

/-- The underlying derived module of restricted pullback is ambient derived pullback. -/
@[simp]
theorem pullback.obj_obj {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    ((pullback f).obj E).obj =
      (RingedSpace.modulePullbackDerived f.toLRSHom.toShHom).obj E.obj := sorry

/-- The bounded-below derived category `D⁺_QCoh(𝒪_X)`. -/
abbrev Plus (X : Scheme.{u}) :=
  DerivedCategory.Plus.CohomologyIn
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)

/-- The bounded-above derived category `D⁻_QCoh(𝒪_X)`. -/
abbrev Minus (X : Scheme.{u}) :=
  DerivedCategory.Minus.CohomologyIn
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)

/-- The bounded derived category `Dᵇ_QCoh(𝒪_X)`. -/
abbrev Bounded (X : Scheme.{u}) :=
  DerivedCategory.Bounded.CohomologyIn
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)

namespace OpenImmersion

/-- Pullback of modules along an open immersion, bundled as an exact functor. -/
noncomputable def exactPullback {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    X.toRingedSpace.Modules ⥤ₑ U.toRingedSpace.Modules :=
  @RingedSpace.Hom.IsFlat.exactPullback _ _ j.toShHom
    (Scheme.Hom.isFlat_of_flat j)

/-- Derived pullback along an open immersion preserves quasicoherent cohomology. -/
theorem pullbackMapsTo {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace)).inverseImage
          (exactPullback j).mapDerivedCategory := sorry

/-- Derived restriction along an open immersion on the unbounded derived categories with
quasicoherent cohomology. -/
noncomputable def pullback {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace) :=
  ObjectProperty.FullSubcategory.restrict
    (exactPullback j).mapDerivedCategory
    (pullbackMapsTo j)

/-- Bounded-below derived pullback along an open immersion preserves quasicoherent
cohomology. -/
theorem pullbackPlusMapsTo {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace)).inverseImage
          (ExactFunctor.Derived.Plus.functor (exactPullback j)) := sorry

/-- Derived restriction along an open immersion on the bounded-below derived categories
with quasicoherent cohomology. -/
noncomputable def pullbackPlus {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Plus X ⥤ Plus U :=
  ObjectProperty.FullSubcategory.restrict
    (ExactFunctor.Derived.Plus.functor (exactPullback j))
    (pullbackPlusMapsTo j)

/-- Bounded-above derived pullback along an open immersion preserves quasicoherent
cohomology. -/
theorem pullbackMinusMapsTo {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory.Minus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.Minus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace)).inverseImage
          (ExactFunctor.Derived.Minus.functor (exactPullback j)) := sorry

/-- Derived restriction along an open immersion on the bounded-above derived categories
with quasicoherent cohomology. -/
noncomputable def pullbackMinus {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Minus X ⥤ Minus U :=
  ObjectProperty.FullSubcategory.restrict
    (ExactFunctor.Derived.Minus.functor (exactPullback j))
    (pullbackMinusMapsTo j)

/-- Bounded derived pullback along an open immersion preserves quasicoherent cohomology. -/
theorem pullbackBoundedMapsTo {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory.Bounded.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.Bounded.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace)).inverseImage
          (ExactFunctor.Derived.Bounded.functor (exactPullback j)) := sorry

/-- Derived restriction along an open immersion on the bounded derived categories with
quasicoherent cohomology. -/
noncomputable def pullbackBounded {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Bounded X ⥤ Bounded U :=
  ObjectProperty.FullSubcategory.restrict
    (ExactFunctor.Derived.Bounded.functor (exactPullback j))
    (pullbackBoundedMapsTo j)

end OpenImmersion

end AlgebraicGeometry.Scheme.DerivedQCoh
