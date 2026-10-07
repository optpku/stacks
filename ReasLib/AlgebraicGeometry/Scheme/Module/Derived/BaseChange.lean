module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.DerivedBaseChange

variable {X X' S S' : Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f'.toShHom)]
variable [hleft : IsIso
  (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
variable [hright : IsIso
  (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]

/-- The canonical unbounded derived base-change transformation associated to a commutative
square of schemes. -/
noncomputable def map (sq : CommSq g' f' f g) :
    RingedSpace.Hom.DerivedBaseChange.source f.toShHom g.toShHom ⟶
      RingedSpace.Hom.DerivedBaseChange.target g'.toShHom f'.toShHom :=
  RingedSpace.Hom.DerivedBaseChange.map
    (RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom)
    (RingedSpace.modulePullbackDerivedPushforwardAdjunction f'.toShHom)
    (@RingedSpace.Hom.DerivedBaseChange.pullbackIsoOfIsIso _ _ _ _
      g'.toShHom f'.toShHom f.toShHom g.toShHom
      ((sq.map (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace)) :
          CommSq g'.toShHom f'.toShHom f.toShHom g.toShHom)
      hleft hright)

/-- The scheme-level derived base-change transformation satisfies the canonical mate
specification. -/
theorem map_isMap (sq : CommSq g' f' f g) :
    RingedSpace.Hom.DerivedBaseChange.IsMap
      (RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom)
      (RingedSpace.modulePullbackDerivedPushforwardAdjunction f'.toShHom)
      (@RingedSpace.Hom.DerivedBaseChange.pullbackIsoOfIsIso _ _ _ _
        g'.toShHom f'.toShHom f.toShHom g.toShHom
        ((sq.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace)) :
            CommSq g'.toShHom f'.toShHom f.toShHom g.toShHom)
        hleft hright)
      (map sq) := sorry

end AlgebraicGeometry.Scheme.Hom.DerivedBaseChange

namespace AlgebraicGeometry.Scheme.TorIndependentBaseChange

variable {Z' Z X' X : Scheme.{u}}

/-- For a Tor-independent cartesian square whose map `i : Z ⟶ X` is a closed immersion,
the canonical unbounded derived base-change transformation is invertible. -/
theorem map_isIso_of_isClosedImmersion
    (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (f : X' ⟶ X)
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom i.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom i'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison i'.toShHom f.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g.toShHom i.toShHom)]
    (sq : IsPullback g i' i f) [IsClosedImmersion i]
    (hTor : Scheme.TorIndependentOver (Over.mk i) (Over.mk f)) :
    IsIso (Scheme.Hom.DerivedBaseChange.map sq.toCommSq) := sorry

end AlgebraicGeometry.Scheme.TorIndependentBaseChange
