/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Valuative realization of specializations on schemes
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace _root_.Specializes


/-- A valuative realization of two points in a scheme carries a chosen map from the residue field
of the general point to its prescribed field. The specialization proof is deliberately not part
of the data. -/
@[stacks 01J8 "valuative realization of a specialization"]
structure ValuationRealization {S : Scheme.{u}} (s' s : S) {K : Type u} [Field K]
    (i : S.residueField s' ⟶ CommRingCat.of K) where
  /-- The valuation subring realizing the two points. -/
  V : ValuationSubring K
  /-- The morphism from the spectrum of the realizing valuation subring. -/
  hom : Spec (CommRingCat.of V) ⟶ S
  /-- Compatibility with the chosen residue-field map at the general point. -/
  genericSq :
    CommSq (Spec.map i)
      (Spec.map (CommRingCat.ofHom (algebraMap V K)))
      (S.fromSpecResidueField s') hom
  /-- The closed point maps to the prescribed special point. -/
  map_closedPoint : hom (IsLocalRing.closedPoint V) = s

namespace ValuationRealization

/-- Read the chosen residue-field map of a valuative realization. -/
@[stacks 01J8 "valuative realization residue-field map"]
abbrev residueFieldMap {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K}
    (_ : ValuationRealization s' s i) : S.residueField s' ⟶ CommRingCat.of K := i

/-- Transport a valuative realization across an equality of its prescribed residue-field maps. -/
@[stacks 01J8 "valuative realization map-index transport"]
def cast {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i j : S.residueField s' ⟶ CommRingCat.of K} (h : i = j)
    (D : ValuationRealization s' s i) : ValuationRealization s' s j :=
  h ▸ D

/-- Transport along reflexivity leaves a valuative realization unchanged. -/
@[simp, stacks 01J8 "valuative realization map-index transport reflexivity"]
theorem cast_rfl {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K} (D : ValuationRealization s' s i) :
    D.cast rfl = D := sorry

attribute [stacks 01J8 "valuative realization subring"] ValuationRealization.V
attribute [stacks 01J8 "valuative realization scheme morphism"] ValuationRealization.hom
attribute [stacks 01J8 "valuative realization generic square"] ValuationRealization.genericSq
attribute [stacks 01J8 "valuative realization closed-point equation"]
  ValuationRealization.map_closedPoint

/-- The canonical map from the spectrum of the prescribed field to the ambient scheme. -/
@[stacks 01J8 "generic map of a valuative realization"]
noncomputable def genericMap {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K} (D : ValuationRealization s' s i) :
    Spec (CommRingCat.of K) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap D.V K)) ≫ D.hom

/-- The generic map sends the closed point of the prescribed field to the general point. -/
@[simp, stacks 01J8 "generic map closed-point readout"]
theorem genericMap_closedPoint {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K} (D : ValuationRealization s' s i) :
    D.genericMap (IsLocalRing.closedPoint K) = s' := sorry

/-- The canonical field-valued map is the map prescribed by the generic-point square. -/
@[stacks 01J8 "valuative realization generic-map equation"]
theorem genericMap_eq {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K} (D : ValuationRealization s' s i) :
    D.genericMap = Spec.map D.residueFieldMap ≫ S.fromSpecResidueField s' := sorry

/-- Postcompose a valuative realization with any scheme morphism to obtain Mathlib's valuative
square. The chosen generic and valuation-spectrum maps remain the explicit data; only the
commutativity proof is supplied by the adapter. -/
@[stacks 01J8 "valuative realization as a Mathlib valuative square"]
noncomputable def toValuativeCommSq {S T : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K}
    (D : ValuationRealization s' s i) (f : S ⟶ T) :
    AlgebraicGeometry.ValuativeCommSq f where
  R := D.V
  K := K
  i₁ := D.genericMap
  i₂ := D.hom ≫ f
  commSq := sorry

/-- The generic point maps to the prescribed general point. -/
@[stacks 01J8 "generic endpoint of a bundled valuative realization"]
theorem map_genericPoint {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K} (D : ValuationRealization s' s i) :
    D.hom (genericPoint (Spec (CommRingCat.of D.V))) = s' := sorry

/-- The defining generic-square and closed-endpoint conditions of a valuative realization. -/
@[stacks 01J8 "valuative realization specification"]
theorem spec {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K} (D : ValuationRealization s' s i) :
    CommSq (Spec.map D.residueFieldMap)
        (Spec.map (CommRingCat.ofHom (algebraMap D.V K)))
        (S.fromSpecResidueField s') D.hom ∧
      D.hom (IsLocalRing.closedPoint D.V) = s := sorry

/-- The endpoints of a valuative realization are related by specialization. -/
@[stacks 01J8 "specialization underlying a valuative realization"]
theorem specializes {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    {i : S.residueField s' ⟶ CommRingCat.of K} (D : ValuationRealization s' s i) :
    s' ⤳ s := sorry

/-- A specialization admits a bundled valuative realization for any chosen residue-field map. -/
@[stacks 01J8 "existence of a bundled valuative realization"]
theorem nonempty {S : Scheme.{u}} {s' s : S} (hsp : s' ⤳ s)
    {K : Type u} [Field K] (i : S.residueField s' ⟶ CommRingCat.of K) :
    Nonempty (ValuationRealization s' s i) := sorry

/-- A bundled valuative realization exists exactly for a specialization. -/
@[stacks 01J8 "valuative realization nonemptiness criterion"]
theorem nonempty_iff_specializes {S : Scheme.{u}} {s' s : S} {K : Type u} [Field K]
    (i : S.residueField s' ⟶ CommRingCat.of K) :
    Nonempty (ValuationRealization s' s i) ↔ s' ⤳ s := sorry

end ValuationRealization

/-- The generic endpoint is determined by a residue-field square through any fraction field. -/
@[stacks 01J8 "fraction-field generic endpoint from residue-field square"]
theorem map_genericPoint_of_fractionSq
    {S : Scheme.{u}} {s' : S} {R K : Type u}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (i : S.residueField s' ⟶ CommRingCat.of K)
    (f : Spec (CommRingCat.of R) ⟶ S)
    (sq : CommSq (Spec.map i)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (S.fromSpecResidueField s') f) :
    f (genericPoint (Spec (CommRingCat.of R))) = s' := sorry

/-- A specialization on a scheme is realized by the generic and closed points of the spectrum of
a valuation ring. -/
@[stacks 01J8]
theorem exists_valuationRing_morphism_basic
    {S : Scheme.{u}} {s' s : S} (hsp : s' ⤳ s) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (f : Spec (CommRingCat.of A) ⟶ S),
      f (genericPoint (Spec (CommRingCat.of A))) = s' ∧
        f (IsLocalRing.closedPoint A) = s := sorry

/-- After prescribing a field extension of the residue field of the general point, the realizing
valuation ring can be chosen as a valuation subring of that field. -/
@[stacks 01J8]
theorem exists_valuationRing_morphism
    {S : Scheme.{u}} {s' s : S} (hsp : s' ⤳ s)
    (K : Type u) [Field K] (i : S.residueField s' ⟶ CommRingCat.of K) :
    ∃ (V : ValuationSubring K) (f : Spec (CommRingCat.of V) ⟶ S),
      CommSq (Spec.map i)
        (Spec.map (CommRingCat.ofHom (algebraMap V K)))
        (S.fromSpecResidueField s') f ∧
      f (IsLocalRing.closedPoint V) = s := sorry

end _root_.Specializes
