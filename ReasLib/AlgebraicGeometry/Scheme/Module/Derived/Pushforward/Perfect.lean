module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- Derived pushforward along a locally finite type morphism to a Noetherian scheme is perfect
for bounded complexes with coherent cohomology, degreewise proper support over the base, and
finite Tor dimension over the inverse-image structure sheaf. -/
theorem pushforward_isPerfect_of_finiteTorDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E)
    (hE_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived X.toRingedSpace)) E)
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf E i)]
    (hE_tor : RingedSpace.HasFiniteTorDimension
      ((RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj E)) :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) := sorry

/-- Derived pushforward along a flat proper morphism to a Noetherian scheme preserves
perfect objects. -/
theorem pushforward_isPerfect_of_flat_of_proper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [Flat f] [IsProper f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) := sorry

/-- Derived pushforward along a perfect proper morphism to a Noetherian scheme preserves
perfect objects. -/
theorem pushforward_isPerfect_of_perfect_of_proper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f]
    [LocallyOfType RingHom.IsPerfectRingMap f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) := sorry

/-- For a flat proper finitely presented morphism, the derived base-change map of a
relatively perfect object is an isomorphism for every cartesian base-change square. -/
theorem pushforward_baseChange_isIso_of_isPerfectRelativeTo
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : IsPerfectRelativeTo f E) :
    IsIso ((Scheme.Hom.DerivedBaseChange.map sq.toCommSq).app E) := sorry

/-- Derived pushforward along a flat proper finitely presented morphism sends objects
perfect relative to the base to perfect objects. -/
theorem pushforward_isPerfect_of_isPerfectRelativeTo
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : IsPerfectRelativeTo f E) :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
