module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 42.46.3 (1): the Chern classes of a derived module are defined when an envelope
makes its derived pullback admit a locally bounded, termwise finite locally free representative. -/
@[stacks 0F9E] #check (AlgebraicGeometry.ChernClass.Derived.IsDefined :
    ∀ {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace),
    Prop)

/- Definition 42.46.3 (2): for a perfect derived module with defined Chern classes, `c(E)` is
the integral total Chern-class family characterized by restriction to every eligible envelope. -/
@[stacks 0F9E] #check (AlgebraicGeometry.ChernClass.Derived.totalClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : ChernClass.Derived.IsDefined E),
    (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)

/- Definition 42.46.3 (3): for a perfect derived module with defined Chern classes, `ch(E)` is
the rational Chern-character family characterized by restriction to every eligible envelope. -/
@[stacks 0F9E] #check (AlgebraicGeometry.ChernClass.Derived.character :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : ChernClass.Derived.IsDefined E),
    (p : ℕ) → TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ π p) ℚ)

/- Definition 42.46.3 (4): for a perfect derived module with defined Chern classes, `P_p(E)` is
the degree-`p` Newton class in the selected integral Newton-class family. -/
@[stacks 0F9E] #check (AlgebraicGeometry.ChernClass.Derived.newtonClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : ChernClass.Derived.IsDefined E),
    (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)
