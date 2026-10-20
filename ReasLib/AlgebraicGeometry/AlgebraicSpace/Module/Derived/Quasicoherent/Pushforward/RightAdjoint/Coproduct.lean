module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Coproduct preservation for the right adjoint of proper flat pushforward

Any right adjoint of restricted derived pushforward along a proper, flat, finitely
presented morphism of algebraic spaces with quasi-compact quasi-separated target
preserves arbitrary direct sums.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Any right adjoint to derived quasicoherent pushforward along a proper, flat,
finite-presentation morphism of algebraic spaces with quasi-compact
quasi-separated target preserves coproducts. -/
theorem rightAdjoint_preservesCoproducts_of_proper_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (I : Type u) :
    PreservesColimitsOfShape (Discrete I) a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
