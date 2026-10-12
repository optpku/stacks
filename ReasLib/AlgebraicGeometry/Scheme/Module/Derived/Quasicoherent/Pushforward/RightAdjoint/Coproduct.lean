/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.FlatCoefficients
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Any right adjoint to derived quasicoherent pushforward along a proper, flat,
finite-presentation morphism with quasi-compact quasi-separated target preserves coproducts. -/
theorem rightAdjoint_preservesCoproducts_of_proper_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
    [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (I : Type u) :
    PreservesColimitsOfShape (Discrete I) a := sorry

/-- Any right adjoint to derived quasicoherent pushforward along a perfect proper
morphism of Noetherian schemes preserves coproducts. -/
theorem rightAdjoint_preservesCoproducts_of_perfect_proper
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] [IsProper f]
    [LocallyOfType RingHom.IsPerfectRingMap f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) a := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
