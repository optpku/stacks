/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Pushforward.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- The derived pushforward of a pseudo-coherent complex along a flat, proper morphism of
finite presentation is pseudo-coherent. -/
theorem pushforward_isPseudoCoherent_of_isPseudoCoherent {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    RingedSpace.ModuleDerived.IsPseudoCoherent
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) := sorry

/-- For a pseudo-coherent complex and any cartesian base-change square, the canonical
derived base-change component for its pushforward is invertible. -/
theorem pushforward_baseChange_isIso_of_isPseudoCoherent
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    IsIso ((DerivedBaseChange.map sq.toCommSq).app E) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
