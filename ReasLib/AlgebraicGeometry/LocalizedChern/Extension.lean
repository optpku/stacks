/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.BaseChange
public import ReasLib.AlgebraicGeometry.BivariantClass.Envelope

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- A localized bivariant class agrees with the graph-localized class on every locally
finite-type cartesian base change satisfying the technical localized-Chern hypotheses. -/
def IsLocalizedClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior)
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)) : Prop :=
  ∀ (X' : Over S) [LocallyOfFiniteType X'.hom]
    (Z' : Scheme.{u}) (i' : Z' ⟶ X'.left) [IsClosedImmersion i']
    (f : X' ⟶ X) [LocallyOfFiniteType f.left]
    (fZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (square : IsPullback fZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left f.left)
    (situation' : Situation S δ X' i'
      ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E) p mode),
    BivariantClass.restrict δ fZ
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') f square (p : ℤ) c =
      graphLocalizedClass i' (classes.reanchor X') situation'

/-- Under the technical localized-Chern hypotheses, the restriction specification
characterizes the graph-localized class. -/
theorem isLocalizedClass_iff_eq_graphLocalizedClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} (situation : Situation S δ X i E p mode)
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)) :
    IsLocalizedClass i classes E p mode c ↔ c = graphLocalizedClass i classes situation :=
  sorry

/-- A perfect complex with defined Chern classes and the specified behavior away from
a closed center admits a unique localized bivariant class agreeing with the
graph-localized classes on all technically admissible locally finite-type base changes. -/
theorem existsUnique_of_isDefined
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (offCenter : OffCenterCondition i E p mode)
    (hDefined : ChernClass.Derived.IsDefined E) :
    ∃! c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      IsLocalizedClass i classes E p mode c :=
  sorry

end AlgebraicGeometry.LocalizedChern
