module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Valuation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete valuative realizations of specializations

This file refines a valuative realization to a discrete valuation ring under
locally Noetherian hypotheses. The general valuation-ring realization remains
in `ReasLib.AlgebraicGeometry.Scheme.Topology.Valuation`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace _root_.Specializes

/-- A realization of two points by the generic and closed points of the spectrum of a discrete
valuation ring. The specialization proof is deliberately not part of the data. -/
@[stacks 054F "DVR realization of a specialization"]
structure DvrRealization {X : Scheme.{u}} (x' x : X) where
  /-- The discrete valuation ring realizing the two points. -/
  R : Type u
  /-- The commutative-ring structure on the realizing ring. -/
  [commRing : CommRing R]
  /-- The realizing ring is a domain. -/
  [domain : IsDomain R]
  /-- The realizing ring is a discrete valuation ring. -/
  [dvr : IsDiscreteValuationRing R]
  /-- The morphism from the spectrum of the realizing ring. -/
  hom : Spec (CommRingCat.of R) ⟶ X
  /-- The generic point maps to the prescribed general point. -/
  map_genericPoint : hom (genericPoint (Spec (CommRingCat.of R))) = x'
  /-- The closed point maps to the prescribed special point. -/
  map_closedPoint : hom (IsLocalRing.closedPoint R) = x

attribute [stacks 054F "DVR realization ring"] DvrRealization.R
attribute [stacks 054F "DVR realization commutative-ring structure"] DvrRealization.commRing
attribute [stacks 054F "DVR realization domain structure"] DvrRealization.domain
attribute [stacks 054F "DVR realization discrete-valuation structure"] DvrRealization.dvr
attribute [stacks 054F "DVR realization scheme morphism"] DvrRealization.hom
attribute [stacks 054F "DVR realization generic-point equation"]
  DvrRealization.map_genericPoint
attribute [stacks 054F "DVR realization closed-point equation"]
  DvrRealization.map_closedPoint

namespace DvrRealization

/-- The spectrum of the realizing discrete valuation ring. -/
@[stacks 054F "spectrum of a DVR realization"]
noncomputable def spectrum {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    Scheme.{u} := by
  -- Local instance justification (defeq pin): use the commutative-ring structure stored in D to form its spectrum.
  letI : CommRing D.R := D.commRing
  exact Spec (CommRingCat.of D.R)

/-- The generic point of the spectrum of the realizing discrete valuation ring. -/
@[stacks 054F "generic point of a DVR realization"]
noncomputable def genericPoint {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    D.spectrum := by
  -- Local instance justification (defeq pin): use the commutative-ring structure stored in D to identify its spectrum.
  letI : CommRing D.R := D.commRing
  -- Local instance justification (defeq pin): use the domain structure stored in D to select the generic point.
  letI : IsDomain D.R := D.domain
  exact _root_.genericPoint (Spec (CommRingCat.of D.R))

/-- The closed point of the spectrum of the realizing discrete valuation ring. -/
@[stacks 054F "closed point of a DVR realization"]
noncomputable def closedPoint {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    D.spectrum := by
  -- Local instance justification (defeq pin): use the commutative-ring structure stored in D to identify its spectrum.
  letI : CommRing D.R := D.commRing
  -- Local instance justification (defeq pin): use the domain structure stored in D when recovering its local-ring structure.
  letI : IsDomain D.R := D.domain
  -- Local instance justification (defeq pin): use the discrete-valuation structure stored in D to select its closed point.
  letI : IsDiscreteValuationRing D.R := D.dvr
  exact IsLocalRing.closedPoint D.R

/-- The spectrum of the fraction field of the realizing discrete valuation ring. -/
@[stacks 054F "fraction-field spectrum of a DVR realization"]
noncomputable def fractionSpectrum {X : Scheme.{u}} {x' x : X}
    (D : DvrRealization x' x) : Scheme.{u} := by
  -- Local instance justification (defeq pin): use the commutative-ring structure stored in D to form its fraction ring.
  letI : CommRing D.R := D.commRing
  -- Local instance justification (defeq pin): use the domain structure stored in D to form its fraction ring.
  letI : IsDomain D.R := D.domain
  exact Spec (CommRingCat.of (FractionRing D.R))

/-- The unique point of the spectrum of the fraction field of a DVR realization. -/
@[stacks 054F "fraction-field point of a DVR realization"]
noncomputable def fractionPoint {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    D.fractionSpectrum := by
  -- Local instance justification (defeq pin): use the commutative-ring structure stored in D to form its fraction field.
  letI : CommRing D.R := D.commRing
  -- Local instance justification (defeq pin): use the domain structure stored in D to form its fraction field.
  letI : IsDomain D.R := D.domain
  exact IsLocalRing.closedPoint (FractionRing D.R)

/-- The canonical map from the spectrum of the fraction field of a DVR realization to the ambient
scheme. -/
@[stacks 054F "generic map of a DVR realization"]
noncomputable def genericMap {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    D.fractionSpectrum ⟶ X := by
  -- Local instance justification (defeq pin): use the commutative-ring structure stored in D to form the fraction-field map.
  letI : CommRing D.R := D.commRing
  -- Local instance justification (defeq pin): use the domain structure stored in D to form the fraction-field map.
  letI : IsDomain D.R := D.domain
  exact Spec.map (CommRingCat.ofHom (algebraMap D.R (FractionRing D.R))) ≫ D.hom

/-- The generic map of a DVR realization sends the field-spectrum point to the general point. -/
@[simp, stacks 054F "DVR generic-map closed-point readout"]
theorem genericMap_closedPoint {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    D.genericMap D.fractionPoint = x' := sorry

/-- Postcomposing a DVR realization with a scheme morphism `f` yields a valuative square whose
generic-side map is `D.genericMap` and whose valuation-side map is `D.hom ≫ f`. -/
@[stacks 054F "DVR realization as a Mathlib valuative square"]
noncomputable def toValuativeCommSq {X Y : Scheme.{u}} {x' x : X}
    (D : DvrRealization x' x) (f : X ⟶ Y) :
    AlgebraicGeometry.ValuativeCommSq f := by
  -- Local instance justification (defeq pin): use the commutative-ring structure stored in D in the valuative square.
  letI : CommRing D.R := D.commRing
  -- Local instance justification (defeq pin): use the domain structure stored in D in the valuative square.
  letI : IsDomain D.R := D.domain
  -- Local instance justification (defeq pin): use the discrete-valuation structure stored in D to infer its valuation-ring structure.
  letI : IsDiscreteValuationRing D.R := D.dvr
  exact
    { R := D.R
      K := FractionRing D.R
      i₁ := D.genericMap
      i₂ := D.hom ≫ f
      commSq := sorry }

/-- The defining endpoint conditions of a DVR realization. -/
@[stacks 054F "DVR realization specification"]
theorem spec {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    D.hom D.genericPoint = x' ∧ D.hom D.closedPoint = x := sorry

/-- The endpoints of a DVR realization are related by specialization. -/
@[stacks 054F "specialization underlying a DVR realization"]
theorem specializes {X : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) :
    x' ⤳ x := sorry

/-- A specialization in a locally Noetherian scheme admits a bundled realization by the generic
and closed points of the spectrum of a discrete valuation ring. -/
@[stacks 054F]
theorem nonempty {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X} (h : x' ⤳ x) :
    Nonempty (DvrRealization x' x) := sorry

/-- A DVR realization exists exactly for a specialization on a locally Noetherian scheme. -/
@[stacks 054F "DVR realization nonemptiness criterion"]
theorem nonempty_iff_specializes {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X} :
    Nonempty (DvrRealization x' x) ↔ x' ⤳ x := sorry

/-- A DVR realization inside a prescribed field `K`, indexed by the explicit residue-field map.
The realizing ring is represented as a valuation subring of `K`, so its inclusion into `K` and
its fraction-field structure are canonical. -/
@[stacks 054F "map-oriented DVR realization with prescribed field"]
structure WithFieldMap {X : Scheme.{u}} (x' x : X) {K : Type u} [Field K]
    (i : X.residueField x' ⟶ CommRingCat.of K)
    extends ValuationRealization x' x i where
  /-- The realizing valuation subring is discrete. -/
  [dvr : IsDiscreteValuationRing V]

attribute [stacks 054F "map-oriented DVR valuative realization"]
  WithFieldMap.toValuationRealization
attribute [stacks 054F "map-oriented DVR discrete valuation property"] WithFieldMap.dvr

namespace WithFieldMap

/-- Transport a map-oriented DVR realization across an equality of its prescribed residue-field
maps. -/
@[stacks 054F "map-oriented DVR map-index transport"]
def cast {X : Scheme.{u}} {x' x : X} {K : Type u} [Field K]
    {i j : X.residueField x' ⟶ CommRingCat.of K} (h : i = j)
    (D : WithFieldMap x' x i) : WithFieldMap x' x j :=
  h ▸ D

/-- Transport along reflexivity leaves a map-oriented DVR realization unchanged. -/
@[simp, stacks 054F "map-oriented DVR map-index transport reflexivity"]
theorem cast_rfl {X : Scheme.{u}} {x' x : X} {K : Type u} [Field K]
    {i : X.residueField x' ⟶ CommRingCat.of K} (D : WithFieldMap x' x i) :
    D.cast rfl = D := sorry

/-- Read the prescribed residue-field map of a map-oriented DVR realization. -/
@[stacks 054F "map-oriented DVR residue-field map"]
abbrev residueFieldMap
    {X : Scheme.{u}} {x' x : X} {K : Type u} [Field K]
    {i : X.residueField x' ⟶ CommRingCat.of K} (_ : WithFieldMap x' x i) :
    X.residueField x' ⟶ CommRingCat.of K :=
  i

/-- The generic map of a map-oriented DVR realization, with source `Spec K`. -/
@[stacks 054F "map-oriented DVR generic map"]
noncomputable abbrev genericMap {X : Scheme.{u}} {x' x : X} {K : Type u} [Field K]
    {i : X.residueField x' ⟶ CommRingCat.of K} (D : WithFieldMap x' x i) :
    Spec (CommRingCat.of K) ⟶ X :=
  D.toValuationRealization.genericMap

/-- Forget the prescribed ambient field and residue-field map of a DVR realization. -/
@[stacks 054F "underlying DVR realization"]
def toDvrRealization {X : Scheme.{u}} {x' x : X} {K : Type u} [Field K]
    {i : X.residueField x' ⟶ CommRingCat.of K} (D : WithFieldMap x' x i) :
    DvrRealization x' x where
  R := D.V
  commRing := inferInstance
  domain := inferInstance
  dvr := D.dvr
  hom := D.hom
  map_genericPoint := D.toValuationRealization.map_genericPoint
  map_closedPoint := D.map_closedPoint

/-- The prescribed generic map is recovered from the underlying DVR generic map through the
canonical fraction-ring equivalence. -/
@[stacks 054F "map-oriented DVR generic-map comparison"]
theorem genericMap_toDvr
    {X : Scheme.{u}} {x' x : X} {K : Type u} [Field K]
    {i : X.residueField x' ⟶ CommRingCat.of K} (D : WithFieldMap x' x i) :
    D.genericMap =
      Spec.map (CommRingCat.ofHom (FractionRing.algEquiv D.V K).toRingHom) ≫
        D.toDvrRealization.genericMap := sorry

/-- A nontrivial specialization admits a map-oriented DVR realization when the prescribed
residue-field map is of finite type. -/
@[stacks 054F "existence of a map-oriented DVR realization"]
theorem nonempty {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X}
    (h : x' ⤳ x) (h_ne : x ≠ x') {K : Type u} [Field K]
    (i : X.residueField x' ⟶ CommRingCat.of K) (hfin : i.hom.FiniteType) :
    Nonempty (WithFieldMap x' x i) := sorry

end WithFieldMap

/-- The Algebra-facing specialization of `WithFieldMap` for a prescribed fraction field. -/
@[stacks 054F "DVR realization with prescribed fraction field"]
abbrev WithFractionField {X : Scheme.{u}} (x' x : X) (K : Type u) [Field K]
    [Algebra (X.residueField x') K] :=
  WithFieldMap x' x (CommRingCat.ofHom (algebraMap (X.residueField x') K))

namespace WithFractionField

/-- A nontrivial specialization in a locally Noetherian scheme admits a bundled DVR realization
inside any prescribed finite-type extension of the residue field of its general point. -/
@[stacks 054F]
theorem nonempty {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X}
    (h : x' ⤳ x) (h_ne : x ≠ x') (K : Type u) [Field K]
    [Algebra (X.residueField x') K] [Algebra.FiniteType (X.residueField x') K] :
    Nonempty (WithFractionField x' x K) := sorry

end WithFractionField

end DvrRealization

/-- A specialization in a locally Noetherian scheme admits a morphism from the spectrum of a
discrete valuation ring whose generic and closed points map to `x'` and `x`. -/
@[stacks 054F]
theorem exists_discreteValuationRing_morphism
    {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X} (h : x' ⤳ x) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (f : Spec (CommRingCat.of R) ⟶ X),
      f (genericPoint (Spec (CommRingCat.of R))) = x' ∧
        f (IsLocalRing.closedPoint R) = x := sorry

/-- A nontrivial specialization admits a discrete valuation realization inside any prescribed
finite-type field extension of the residue field of its general point. -/
@[stacks 054F]
theorem exists_discreteValuationRing_morphism_with_prescribed_fractionField
    {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X} (h : x' ⤳ x) (hneq : x ≠ x')
    (K : Type u) [Field K] [Algebra (X.residueField x') K]
    [Algebra.FiniteType (X.residueField x') K] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (_ : Algebra R K) (_ : IsFractionRing R K)
      (f : Spec (CommRingCat.of R) ⟶ X),
      f (genericPoint (Spec (CommRingCat.of R))) = x' ∧
        f (IsLocalRing.closedPoint R) = x ∧
        CommSq
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') K)))
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (X.fromSpecResidueField x') f := sorry

end _root_.Specializes
