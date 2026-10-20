/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Definedness
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/- Lemma 42.46.4 (1): an envelope with a locally bounded finite locally free representative
ensures defined Chern classes. This criterion holds for arbitrary schemes and derived modules,
so it applies in particular to the perfect objects over the base of Situation 42.7.1. -/
@[stacks 0GUE] #check (AlgebraicGeometry.ChernClass.Derived.IsDefined.ofEnvelope :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsEnvelope f]
    {E : RingedSpace.ModuleDerived X.toRingedSpace}
    (hRep : RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((RingedSpace.modulePullbackDerived f.toShHom).obj E)),
    IsDefined E)

/- Lemma 42.46.4 (2): a bounded finite locally free representative ensures defined Chern
classes. Neither perfectness nor a chosen base is needed for this stronger criterion. -/
@[stacks 0GUE] #check (AlgebraicGeometry.ChernClass.Derived.isDefined_of_boundedRepresentative :
    ∀ {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : CochainComplex X.Modules ℤ)
    (hRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K),
    IsDefined E)

/- Lemma 42.46.4 (3): quasi-compact irreducible components ensure defined Chern classes for
a perfect object on a locally Noetherian scheme. Under Situation 42.7.1, the base is locally
Noetherian by UniversallyCatenary.toIsLocallyNoetherian, and a scheme locally of finite type
over it is locally Noetherian by LocallyOfFiniteType.isLocallyNoetherian. Thus this stronger
criterion specializes to the source hypotheses without requiring finitely many components. -/
@[stacks 0GUE] #check (AlgebraicGeometry.ChernClass.Derived.isDefined_of_compactComponents :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hComponents : ∀ Z : irreducibleComponents X, IsCompact (Z : Set X)),
    IsDefined E)

/- Lemma 42.46.4 (4): a perfect derived module on a quasi-compact locally Noetherian scheme
has defined Chern classes. As in part (3), the locally finite-type hypothesis over the base of
Situation 42.7.1 supplies local Noetherianness. -/
@[stacks 0GUE] #check (AlgebraicGeometry.ChernClass.Derived.isDefined_of_compactSpace :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E),
    IsDefined E)

/- Lemma 42.46.4 (5): an object isomorphic to the derived pullback of an object with defined
Chern classes has defined Chern classes. This holds for arbitrary scheme morphisms and derived
modules, hence in particular for the perfect objects and morphisms over the given base. -/
@[stacks 0GUE] #check (AlgebraicGeometry.ChernClass.Derived.isDefined_of_pullback :
    ∀ {X X' : Scheme.{u}} (g : X ⟶ X')
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (E' : RingedSpace.ModuleDerived X'.toRingedSpace)
    (hDefined' : IsDefined E')
    (hPullback : IsIsomorphic
      ((RingedSpace.modulePullbackDerived g.toShHom).obj E') E),
    IsDefined E)

end AlgebraicGeometry.ChernClass.Derived
