module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence

/-!
# Lower bound for the right adjoint of derived pushforward

A chosen right adjoint of restricted derived pushforward on `DerivedQCoh`
along a morphism of quasi-compact quasi-separated algebraic spaces preserves
lower cohomological bounds up to a uniform integer shift.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A right adjoint to derived quasicoherent pushforward along a morphism of
quasi-compact quasi-separated algebraic spaces preserves lower cohomological bounds
up to a uniform integer shift. -/
theorem rightAdjoint_uniformLowerBound {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn f ⊣ a) :
    ∃ N : ℤ, ∀ (K : DerivedQCoh Y) (c : ℤ),
      K.obj.IsGE (c + 1) → (a.obj K).obj.IsGE (c - N + 1) :=
  sorry

/-- A right adjoint to derived quasicoherent pushforward along a morphism of
quasi-compact quasi-separated algebraic spaces sends bounded-below objects to
bounded-below objects. -/
theorem rightAdjoint_mapsBoundedBelow {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn f ⊣ a) (K : DerivedQCoh Y)
    (hK : K.obj.IsBoundedBelow) : (a.obj K).obj.IsBoundedBelow :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
