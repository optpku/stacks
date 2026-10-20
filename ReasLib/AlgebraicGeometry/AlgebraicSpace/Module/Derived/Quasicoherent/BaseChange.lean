module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.Adjunction

/-! # Derived base change with quasi-coherent cohomology

The canonical derived base-change transformation restricts to complexes with
quasi-coherent cohomology and is invertible for Tor-independent cartesian squares.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The canonical derived base-change transformation on complexes with quasi-coherent
cohomology. -/
noncomputable def map
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : CommSq g' f' f g) :
    pushforwardCohomologyIn f ⋙ pullback g ⟶ pullback g' ⋙ pushforwardCohomologyIn f' where
  app E := ObjectProperty.homMk
    ((pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
      (Functor.LeftDerived.Homotopy.functor (Modules.pullback g)).map
        ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
      (Hom.DerivedBaseChange.map sq).app E.obj ≫
      (Modules.moduleDerivedPushforward f').map
        ((pullback.inclusionIso g').inv.app E) ≫
      (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E))
  naturality _ _ _ := sorry

/-- Forgetting quasi-coherent cohomology from the derived base-change map recovers the
canonical ambient derived base-change component. -/
theorem map_app_hom
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : CommSq g' f' f g) (E : DerivedQCoh X) :
    ((map g' f' f g sq).app E).hom =
      (pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
        (Functor.LeftDerived.Homotopy.functor (Modules.pullback g)).map
          ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
        (Hom.DerivedBaseChange.map sq).app E.obj ≫
        (Modules.moduleDerivedPushforward f').map
          ((pullback.inclusionIso g').inv.app E) ≫
        (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E) :=
  sorry

/-- Tor independence makes the canonical base-change transformation on `DerivedQCoh`
invertible. -/
theorem map_isIso_of_torIndependent
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (map g' f' f g sq.toCommSq) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
