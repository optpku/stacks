/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.TorIndependence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction

public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange

variable {X' X Y' Y : Scheme.{u}}

/-- Naturality of the ambient derived base-change components after lifting them to
derived objects with quasicoherent cohomology. -/
private theorem map_naturality
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : CommSq g' f' f g) {E F : DerivedQCoh X} (φ : E ⟶ F) :
    (pushforwardCohomologyIn f ⋙ pullback g).map φ ≫
        ObjectProperty.homMk
          ((pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj F) ≫
            (RingedSpace.modulePullbackDerived g.toShHom).map
              ((pushforwardCohomologyIn.inclusionIso f).hom.app F) ≫
            (@Scheme.Hom.DerivedBaseChange.map _ _ _ _ g' f' f g
              (pullbackPushforwardAdjunctionHasPair f)
              (pullbackPushforwardAdjunctionHasPair f')
              (RingedSpace.modulePullbackDerived.compComparison_isIso f'.toShHom g.toShHom)
              (RingedSpace.modulePullbackDerived.compComparison_isIso g'.toShHom f.toShHom)
              sq).app F.obj ≫
            (RingedSpace.moduleDerivedPushforward f'.toShHom).map
              ((pullback.inclusionIso g').inv.app F) ≫
            (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj F)) =
      ObjectProperty.homMk
          ((pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
            (RingedSpace.modulePullbackDerived g.toShHom).map
              ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
            (@Scheme.Hom.DerivedBaseChange.map _ _ _ _ g' f' f g
              (pullbackPushforwardAdjunctionHasPair f)
              (pullbackPushforwardAdjunctionHasPair f')
              (RingedSpace.modulePullbackDerived.compComparison_isIso f'.toShHom g.toShHom)
              (RingedSpace.modulePullbackDerived.compComparison_isIso g'.toShHom f.toShHom)
              sq).app E.obj ≫
            (RingedSpace.moduleDerivedPushforward f'.toShHom).map
              ((pullback.inclusionIso g').inv.app E) ≫
            (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E)) ≫
        (pullback g' ⋙ pushforwardCohomologyIn f').map φ := sorry

/-- The canonical derived base-change transformation on complexes with quasicoherent
cohomology. -/
noncomputable def map
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : CommSq g' f' f g) :
    pushforwardCohomologyIn f ⋙ pullback g ⟶ pullback g' ⋙ pushforwardCohomologyIn f' where
  app E := ObjectProperty.homMk
    ((pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
      (RingedSpace.modulePullbackDerived g.toShHom).map
        ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
      (@Scheme.Hom.DerivedBaseChange.map _ _ _ _ g' f' f g
        (pullbackPushforwardAdjunctionHasPair f)
        (pullbackPushforwardAdjunctionHasPair f')
        (RingedSpace.modulePullbackDerived.compComparison_isIso f'.toShHom g.toShHom)
        (RingedSpace.modulePullbackDerived.compComparison_isIso g'.toShHom f.toShHom)
        sq).app E.obj ≫
      (RingedSpace.moduleDerivedPushforward f'.toShHom).map
        ((pullback.inclusionIso g').inv.app E) ≫
      (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E))
  naturality _ _ φ := map_naturality g' f' f g sq φ

/-- Forgetting quasicoherent cohomology from the derived base-change map recovers the
canonical ambient derived base-change component. -/
theorem map_app_hom
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : CommSq g' f' f g) (E : DerivedQCoh X) :
    ((map g' f' f g sq).app E).hom =
      (pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
        (RingedSpace.modulePullbackDerived g.toShHom).map
          ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
        (@Scheme.Hom.DerivedBaseChange.map _ _ _ _ g' f' f g
          (pullbackPushforwardAdjunctionHasPair f)
          (pullbackPushforwardAdjunctionHasPair f')
          (RingedSpace.modulePullbackDerived.compComparison_isIso f'.toShHom g.toShHom)
          (RingedSpace.modulePullbackDerived.compComparison_isIso g'.toShHom f.toShHom)
          sq).app E.obj ≫
        (RingedSpace.moduleDerivedPushforward f'.toShHom).map
          ((pullback.inclusionIso g').inv.app E) ≫
        (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E) := sorry

/-- Tor independence makes the canonical base-change transformation on `DerivedQCoh`
invertible. -/
theorem map_isIso_of_torIndependent
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (map g' f' f g sq.toCommSq) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange
