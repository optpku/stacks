/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The reduced special-fibre component with index `i`. -/
noncomputable abbrev situationComponent
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) : Scheme.{u} :=
  (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubscheme (components i)

/-- The canonical inclusion of an indexed special-fibre component into the total space. -/
noncomputable abbrev situationComponentInclusion
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) : situationComponent R f n components i ⟶ X :=
  (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι (components i) ≫
    f.fiberι (IsLocalRing.closedPoint R)

/-- The canonical morphism from an indexed component to the residue-field spectrum of the
closed point. -/
noncomputable abbrev situationComponentToResidueField
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) :
    situationComponent R f n components i ⟶
      Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) :=
  (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι (components i) ≫
    f.fiberToSpecResidueField (IsLocalRing.closedPoint R)

/-- Pull an `X`-module back to the indexed special-fibre component. -/
noncomputable abbrev componentRestriction
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (L : X.Modules) (i : Fin n) : (situationComponent R f n components i).Modules :=
  (Scheme.Modules.pullback (situationComponentInclusion R f n components i)).obj L

/-- Component restriction is the canonical module pullback along the component inclusion. -/
theorem componentRestriction_def
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (L : X.Modules) (i : Fin n) :
    componentRestriction R f n components L i =
      (Scheme.Modules.pullback (situationComponentInclusion R f n components i)).obj L := sorry

/-- The curve degree of an invertible module on an indexed special-fibre component. -/
noncomputable def componentDegree
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i, IsProper (situationComponentToResidueField R f n components i))
    (h_component_dimension :
      ∀ i, topologicalKrullDim (situationComponent R f n components i) ≤ 1)
    (i : Fin n) (L : (situationComponent R f n components i).Modules)
    [Scheme.Modules.Invertible L] : ℤ :=
  @Scheme.Modules.curveDegreeOfInvertible _ _ _ _ (h_component_proper i)
    (h_component_dimension i) L inferInstance

/-- Component degree unfolds to the canonical curve degree of the given invertible module. -/
theorem componentDegree_def
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i, IsProper (situationComponentToResidueField R f n components i))
    (h_component_dimension :
      ∀ i, topologicalKrullDim (situationComponent R f n components i) ≤ 1)
    (i : Fin n) (L : (situationComponent R f n components i).Modules)
    [Scheme.Modules.Invertible L] :
    componentDegree R f n components h_component_proper h_component_dimension i L =
      @Scheme.Modules.curveDegreeOfInvertible _ _ _ _ (h_component_proper i)
        (h_component_dimension i) L inferInstance := sorry

end AlgebraicGeometry.Scheme.Hom
