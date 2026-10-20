module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.LocallyFree
import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps.BaseChange

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- A derived module represented by a bounded complex of finite locally free modules has
defined Chern classes. -/
theorem isDefined_of_boundedRepresentative
    {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : CochainComplex X.Modules ℤ)
    (hRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K) :
    IsDefined E := sorry

/-- A perfect derived module on a locally Noetherian scheme with quasi-compact irreducible
components has defined Chern classes. -/
theorem isDefined_of_compactComponents
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hComponents : ∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) :
    IsDefined E := sorry

/-- A perfect derived module on a quasi-compact locally Noetherian scheme has defined
Chern classes. -/
theorem isDefined_of_compactSpace
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) :
    IsDefined E := sorry

/-- A derived module isomorphic to the derived pullback of an object with defined Chern
classes has defined Chern classes. -/
theorem isDefined_of_pullback
    {X X' : Scheme.{u}} (g : X ⟶ X')
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (E' : RingedSpace.ModuleDerived X'.toRingedSpace)
    (hDefined' : IsDefined E')
    (hPullback : IsIsomorphic
      ((RingedSpace.modulePullbackDerived g.toShHom).obj E') E) :
    IsDefined E := sorry

end AlgebraicGeometry.ChernClass.Derived
