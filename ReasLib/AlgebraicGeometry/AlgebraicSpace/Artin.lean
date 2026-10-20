/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Presheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FiniteDimensionalPredeformations
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.Scheme.Presheaf.FiniteTypeFieldBound

/-!
# Artin's criterion for algebraic spaces

A set-valued presheaf satisfying Artin's axioms over a locally Noetherian
base with G-ring stalks at finite-type points is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Over

/-- A presheaf over a locally Noetherian scheme is an algebraic space if its
diagonal is representable by algebraic spaces, its values on finite-type
fields are uniformly bounded, it is an étale sheaf preserving directed affine
limits, its associated groupoid fibration satisfies the Rim-Schlessinger and
finite-dimensionality conditions, all its formal objects are effective,
versality is open, and the base has G-ring stalks at finite-type points. -/
@[stacks 07Y1]
theorem IsAlgebraicSpace.of_artinAxioms {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hΔ : representableByAlgebraicSpaces (diag F))
    (h_size : boundedOnFiniteTypeFields F)
    (h0 : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (h1 : PreservesDirectedAffineLimits S F)
    (hRS : GroupoidsOver.HasRimSchlessinger (toGroupoidsOver F))
    (hT : GroupoidsOver.HasFiniteDimensionalPredeformations (toGroupoidsOver F))
    (h_eff : ∀ ξ : GroupoidsOver.FormalObject (toGroupoidsOver F),
      GroupoidsOver.FormalObject.IsEffective ξ)
    (h_open : GroupoidsOver.OpennessOfVersality (toGroupoidsOver F))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace F :=
  sorry

/-- A presheaf over a locally Noetherian scheme with G-ring stalks at finite-type
points is an algebraic space if it admits a monomorphism into an algebraic space
locally of finite type over the base, is an étale sheaf preserving directed affine
limits, its associated groupoid fibration satisfies the Rim-Schlessinger condition,
all its formal objects are effective, and versality is open. -/
@[stacks 07Y2]
theorem IsAlgebraicSpace.of_mono {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F : (Over S)ᵒᵖ ⥤ Type u} {G : AlgebraicSpace S}
    (a : F ⟶ G.functorOfPoints) [Mono a]
    [LocallyOfFiniteType (SchemeRealization.toBase G)]
    (h0 : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (h1 : PreservesDirectedAffineLimits S F)
    (hRS : GroupoidsOver.HasRimSchlessinger (toGroupoidsOver F))
    (h_eff : ∀ ξ : GroupoidsOver.FormalObject (toGroupoidsOver F),
      GroupoidsOver.FormalObject.IsEffective ξ)
    (h_open : GroupoidsOver.OpennessOfVersality (toGroupoidsOver F))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
