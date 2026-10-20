/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Completion.LocalRing

/-!
# Comparison from Spec to Spf for algebraic-space targets

Restriction along `Spf(R) ⟶ Spec(R)` induces a map on morphisms into an
algebraic space. This map is bijective for complete local Noetherian rings
with their maximal-adic topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The natural map `Mor_S(Spec(R), X) → Mor_S(Spf(R), X)` induced by
precomposition with `spfToSpec`, for an algebraic space `X` over `S`. -/
def specHomToSpfHom_algebraicSpace {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    (AlgebraicSpace.ofOver (Over.mk structureHom) ⟶ X) →
      (spf R structureHom ⟶
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
          X.functorOfPoints) :=
  fun f ↦
    spfToSpec structureHom ≫
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map f

/-- Restricting an algebraic-space morphism to the formal spectrum is
precomposition with `spfToSpec` after sheafifying the morphism. -/
theorem specHomToSpfHom_algebraicSpace_apply {R : Type u} [CommRing R]
    [TopologicalSpace R] [TopologicalRing.IsWeaklyAdmissibleRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (f : AlgebraicSpace.ofOver (Over.mk structureHom) ⟶ X) :
    specHomToSpfHom_algebraicSpace structureHom X f =
      spfToSpec structureHom ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map f :=
  rfl

/-- For a complete local Noetherian `S`-algebra with its maximal-adic topology
and any algebraic space `X` over `S`, restriction from `Spec(R)` to `Spf(R)`
is bijective on morphisms into `X`. -/
theorem specHomToSpfHom_algebraicSpace_bijective {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsNoetherianRing R] [IsCompleteLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S) :
    Function.Bijective (specHomToSpfHom_algebraicSpace structureHom X) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
