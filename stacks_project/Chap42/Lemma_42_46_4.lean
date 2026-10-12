/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Definition_42_46_3_DerivedChern
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.LocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- Lemma 42.46.4 (1): the Chern classes of a perfect derived module are defined if an
envelope makes its derived pullback admit a locally bounded finite locally free representative. -/
@[stacks 0GUE]
theorem isDefined_of_envelope
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [IsEnvelope f]
    (hRep : RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) :
    IsDefined E := sorry

/-- Lemma 42.46.4 (2): the Chern classes of a perfect derived module are defined if it is
represented by a bounded complex of finite locally free modules. -/
@[stacks 0GUE]
theorem isDefined_of_boundedRepresentative
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (K : CochainComplex X.left.Modules ℤ)
    (hRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K) :
    IsDefined E := sorry

/-- Lemma 42.46.4 (3): the Chern classes of a perfect derived module are defined if every
irreducible component of its scheme is quasi-compact. -/
@[stacks 0GUE]
theorem isDefined_of_compactComponents
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hComponents : ∀ Z : irreducibleComponents X.left, IsCompact (Z : Set X.left)) :
    IsDefined E := sorry

/-- Lemma 42.46.4 (4): the Chern classes of a perfect derived module on a quasi-compact scheme
are defined. -/
@[stacks 0GUE]
theorem isDefined_of_compactSpace
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] [CompactSpace X.left]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) :
    IsDefined E := sorry

/-- Lemma 42.46.4 (5): defined Chern classes pull back along a morphism of schemes over the
base, up to isomorphism in the derived category. -/
@[stacks 0GUE]
theorem isDefined_of_pullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X X' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (g : X ⟶ X')
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (E' : RingedSpace.ModuleDerived X'.left.toRingedSpace)
    (hPerfect' : RingedSpace.ModuleDerived.IsPerfect E') (hDefined' : IsDefined E')
    (hPullback : IsIsomorphic
      ((RingedSpace.modulePullbackDerived g.left.toShHom).obj E') E) :
    IsDefined E := sorry

end AlgebraicGeometry.ChernClass.Derived
