module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The tangent functors `T_x` preserve countable products: the canonical
comparison `T_x(∏ᶜ M) ⟶ ∏ᶜ T_x(M n)` is an isomorphism. -/
def tangentFunctor.preservesNatPi {S : Scheme.{u}} (X : GroupoidsOver S)
    [HasStrongRimSchlessinger X] : Prop :=
  ∀ {A : CommRingCat.{u}} {σA : Spec A ⟶ S} (x : X.p.Fiber (Over.mk σA))
    (M : ℕ → ModuleCat.{u} A),
    IsIso (piComparison (tangentFunctor x) M)

/-- `preservesNatPi` means the product comparison of `tangentFunctor x` is an
isomorphism for every fibre object over `Spec(A)` and every countable family of
`A`-modules. -/
theorem tangentFunctor.preservesNatPi_iff {S : Scheme.{u}} (X : GroupoidsOver S)
    [HasStrongRimSchlessinger X] :
    tangentFunctor.preservesNatPi X ↔
      ∀ {A : CommRingCat.{u}} {σA : Spec A ⟶ S} (x : X.p.Fiber (Over.mk σA))
        (M : ℕ → ModuleCat.{u} A),
        IsIso (piComparison (tangentFunctor x) M) :=
  sorry

/-- The product comparison of `T_x` is an isomorphism. -/
theorem tangentFunctor.isIso_piComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] (h : tangentFunctor.preservesNatPi X)
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S} (x : X.p.Fiber (Over.mk σA))
    (M : ℕ → ModuleCat.{u} A) :
    IsIso (piComparison (tangentFunctor x) M) :=
  sorry
end AlgebraicGeometry.GroupoidsOver
