module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale.Localization
public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.Localization
public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.Localization.SeparableClosure
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueField
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueCoordinate
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

@[expose] public section

/-!
# Pointed-etale presentations of strict henselizations

This leaf is the reusable presentation layer for a strict henselization.  The
pointed-etale category and its prime-localization diagram are owned by
CommAlgCat.Over.Etale.Localization; this file only records the residue-field
coordinates, the lifting predicate, and the resulting presentation interface.

The coordinate on the source is canonical: it is induced by the map
R → K whose kernel is p.  The coordinate on the target strict henselization
is supplied explicitly, since an identification of its residue field with an
external field is not canonical.

@stack 04GW
-/

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u v

noncomputable section

namespace IsStrictHenselizationOf.PointedEtale

section

variable {R : Type u} [CommRing R]
variable {K : Type v} [Field K] [Algebra R K]
variable {p : Ideal R} [p.IsPrime]
variable (hbase : RingHom.ker (algebraMap R K) = p)

/-! ### Target coordinate and lifting predicate -/

/-- The residue-field coordinate specialized to the canonical base
localization at `p`.  The neutral coordinate owner lives in
`IsStrictHenselizationOf.ResidueField`; this abbreviation only supplies the
prime-localized base map used by the pointed-etale presentation. -/
@[stacks 04GW "pointed-etale strict-henselization residue coordinate"]
noncomputable abbrev Coordinate
    (hbase : RingHom.ker (algebraMap R K) = p)
    (Rsh : Type v) [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh] :=
  IsStrictHenselizationOf.ResidueField.Coordinate
    (L := Localization.AtPrime p) (S := Rsh) (K := K)
    (CommAlgCat.Over.Target.Localization.baseResidueMap hbase)

namespace Coordinate

variable {Rsh : Type v} [CommRing Rsh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]

/- The generic owner supplies the maximal-ideal coordinate.  This thin
specialization keeps the source-facing namespace stable while avoiding a
second structure definition. -/

/-- The same target coordinate expressed on the maximal-ideal residue field. -/
@[stacks 04GW "maximal-ideal strict-henselization residue coordinate"]
noncomputable abbrev maximalIdealEquiv
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) :
    (maximalIdeal Rsh).ResidueField ≃+* K :=
  IsStrictHenselizationOf.ResidueField.Coordinate.maximalIdealEquiv coordinate

/-- The maximal-ideal form of target-coordinate compatibility. -/
@[stacks 04GW "maximal-ideal residue-coordinate compatibility"]
theorem maximalIdealEquiv_comp
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) :
    (coordinate.maximalIdealEquiv).toRingHom.comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
          (algebraMap (Localization.AtPrime p) Rsh)
          (IsLocalRing.maximalIdeal_comap
            (algebraMap (Localization.AtPrime p) Rsh)).symm) =
      CommAlgCat.Over.Target.Localization.baseResidueFieldMap hbase := sorry

end Coordinate

/-- Source-facing name for the shared underlying localized pointed-etale map.
The relative source algebra is pinned only in the neutral localization owner. -/
@[stacks 04GW "underlying map of a localized pointed-etale morphism"]
noncomputable abbrev ringHom
    {S : Type v} [CommRing S] [Algebra (Localization.AtPrime p) S]
    (A : CommAlgCat.Over.Etale.category R K)
    (f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) S) :
    Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj) →+* S :=
  CommAlgCat.Over.Target.Localization.ringHom hbase A.obj f

/-- A localized algebra morphism is a residue-compatible lift when it induces
the selected pointed-etale residue map. -/
@[stacks 04GW "residue-compatible pointed-etale lift"]
def IsLift
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (A : CommAlgCat.Over.Etale.category R K)
    (f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh) : Prop :=
  ∃ hq :
      maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) =
        Ideal.comap (ringHom hbase A f) (maximalIdeal Rsh),
    (coordinate.maximalIdealEquiv).toRingHom.comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
          (maximalIdeal Rsh) (ringHom hbase A f) hq) =
      CommAlgCat.Over.Target.Localization.residueFieldMap A.obj

/-! ### The lift API -/

/-- A chosen residue-compatible lift.  The map and both residue conditions are
explicit data, so consumers never inspect a witness chosen from an existence
theorem. -/
@[stacks 04GW "chosen pointed-etale strict-henselization lift"]
structure Lift
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (A : CommAlgCat.Over.Etale.category R K) where
  /-- The localized algebra morphism selected by this lift. -/
  hom : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
    CommAlgCat.of (Localization.AtPrime p) Rsh
  /-- The selected map pulls back the target maximal ideal to the selected
  maximal ideal of the localized pointed-etale object. -/
  comap_maximalIdeal :
    maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) =
      Ideal.comap (ringHom hbase A hom) (maximalIdeal Rsh)
  /-- The selected map induces the prescribed maximal-ideal residue coordinate. -/
  residueMap_eq :
    (coordinate.maximalIdealEquiv).toRingHom.comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
          (maximalIdeal Rsh) (ringHom hbase A hom) comap_maximalIdeal) =
      CommAlgCat.Over.Target.Localization.residueFieldMap A.obj

namespace Lift

variable {Rsh : Type v} [CommRing Rsh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
variable (A : CommAlgCat.Over.Etale.category R K)

/- The two defining fields above are exposed individually; this proposition is
the compact source-facing form used by the universal-property theorem. -/
/-- The selected map satisfies the residue-coordinate lifting condition. -/
@[stacks 04GW "specification of a chosen pointed-etale lift"]
theorem spec (lift : Lift (hbase := hbase) coordinate A) :
    IsLift (hbase := hbase) coordinate A lift.hom := sorry

/-- Any two residue-compatible lifts of the same pointed-etale object agree. -/
@[stacks 04GW "uniqueness of a chosen pointed-etale lift"]
theorem unique
    (lift : Lift (hbase := hbase) coordinate A) (g :
      CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
        CommAlgCat.of (Localization.AtPrime p) Rsh)
    (hg : IsLift (hbase := hbase) coordinate A g) :
    g = lift.hom := sorry

end Lift

/-- The localized pointed-etale lifting theorem for a chosen strict
henselization. -/
@[stacks 04GW "unique localized pointed-etale lift"]
theorem existsUnique_lift
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (A : CommAlgCat.Over.Etale.category R K) :
    ∃! f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh,
      IsLift (hbase := hbase) coordinate A f := sorry

/-! ### The localized presentation -/

/-- A natural family of chosen residue-compatible lifts of all pointed-etale
objects.  This is the explicit data owner for a presentation; it does not
hide a Classical.choose witness behind a public non-Prop definition. -/
@[stacks 04GW "pointed-etale strict-henselization presentation data"]
structure Presentation
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) where
  /-- The selected residue-compatible lift at each pointed-etale object. -/
  lift : ∀ A : CommAlgCat.Over.Etale.category R K,
    Lift (hbase := hbase) coordinate A
  /-- Naturality of the selected lifts along pointed-etale morphisms. -/
  naturality : ∀ {A B : CommAlgCat.Over.Etale.category R K} (f : A ⟶ B),
    CommAlgCat.Over.Target.Localization.morphism hbase f.hom ≫ (lift B).hom =
      (lift A).hom

namespace Presentation

variable {Rsh : Type v} [CommRing Rsh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable (coordinate : Coordinate (R := R) (K := K) hbase Rsh)

/-- The naturality field of a presentation in the precise form required by its
localized cocone. -/
@[stacks 04GW "cocone naturality of pointed-etale lifts"]
theorem cocone_naturality
    (presentation : Presentation (hbase := hbase) coordinate)
    {A B : CommAlgCat.Over.Etale.category R K} (f : A ⟶ B) :
    (CommAlgCat.Over.Etale.Localization.diagram hbase).map f ≫
        (presentation.lift B).hom =
      (presentation.lift A).hom ≫
        ((Functor.const (CommAlgCat.Over.Etale.category R K)).obj
          (CommAlgCat.of (Localization.AtPrime p) Rsh)).map f := sorry

/-- The localized cocone determined by a natural family of residue-compatible
lifts. -/
@[stacks 04GW "localized pointed-etale strict-henselization cocone"]
noncomputable def cocone
    (presentation : Presentation (hbase := hbase) coordinate) :
    Cocone (CommAlgCat.Over.Etale.Localization.diagram hbase) where
  pt := CommAlgCat.of (Localization.AtPrime p) Rsh
  ι :=
    { app := fun A => (presentation.lift A).hom
      naturality := fun {A B} f =>
        cocone_naturality (hbase := hbase) coordinate presentation
          (A := A) (B := B) f }

/-- The localized pointed-etale cocone admits a colimit witness.  This is
stated propositionally so the shared interface does not manufacture the
non-Prop `IsColimit` data from a deferred proof. -/
@[stacks 04GW "localized pointed-etale strict-henselization colimit"]
theorem isColimit
    (presentation : Presentation (hbase := hbase) coordinate) :
    Nonempty (IsColimit (cocone (hbase := hbase) coordinate presentation)) := sorry

/-! ### The source presentation -/

/-- The `R`-algebra structure on a strict henselization of `Rₚ`, obtained by
restriction along `R → Rₚ`.  It is a named value rather than a global
instance because it competes with any independently supplied `R`-algebra
structure on the same carrier. -/
@[stacks 04GW "source algebra of a pointed-etale presentation"]
noncomputable abbrev sourceAlgebra :
    Algebra R Rsh :=
  Algebra.restrictScalars R (Localization.AtPrime p) Rsh

/-- The target strict henselization regarded as an object of `CommAlgCat R`
via `sourceAlgebra`. -/
@[stacks 04GW "source object of a pointed-etale presentation"]
noncomputable abbrev sourceObject :
    CommAlgCat R :=
  letI : Algebra R Rsh := sourceAlgebra (R := R) (p := p) (Rsh := Rsh)
  CommAlgCat.of R Rsh

/-- The source-to-localization composite attached to a chosen localized
pointed-etale lift commutes with the restricted `R`-algebra structures. -/
@[stacks 04GW "source map algebra compatibility"]
theorem sourceMap_commutes
    (presentation : Presentation (hbase := hbase) coordinate)
    (A : CommAlgCat.Over.Etale.category R K) (r : R) :
    (ringHom hbase A (presentation.lift A).hom)
        (algebraMap A.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
          (algebraMap R A.obj.left r)) =
      ((algebraMap (Localization.AtPrime p) Rsh).comp
        (algebraMap R (Localization.AtPrime p))) r := sorry

/-- The canonical map from a source pointed-etale algebra to the chosen
strict henselization, obtained by composing its localization map with the
presentation lift. -/
@[stacks 04GW "source map of a pointed-etale presentation"]
noncomputable def sourceMap
    (presentation : Presentation (hbase := hbase) coordinate)
    (A : CommAlgCat.Over.Etale.category R K) :
    (CommAlgCat.Over.Etale.diagram R K).obj A ⟶
      sourceObject (R := R) (p := p) (Rsh := Rsh) :=
  letI : Algebra R Rsh := sourceAlgebra (R := R) (p := p) (Rsh := Rsh)
  CommAlgCat.ofHom {
    toRingHom :=
      (ringHom hbase A (presentation.lift A).hom).comp
        (algebraMap A.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
    commutes' := sourceMap_commutes (hbase := hbase) coordinate presentation A }

/-- The source maps of a presentation are natural in pointed-etale
morphisms. -/
@[stacks 04GW "source map naturality of a pointed-etale presentation"]
theorem sourceMap_naturality
    (presentation : Presentation (hbase := hbase) coordinate)
    {A B : CommAlgCat.Over.Etale.category R K} (f : A ⟶ B) :
    (CommAlgCat.Over.Etale.diagram R K).map f ≫
        sourceMap (hbase := hbase) coordinate presentation B =
      sourceMap (hbase := hbase) coordinate presentation A := sorry

/-- The cocone from the source pointed-etale diagram to the selected strict
henselization. -/
@[stacks 04GW "source pointed-etale strict-henselization cocone"]
noncomputable def sourceCocone
    (presentation : Presentation (hbase := hbase) coordinate) :
    Cocone (CommAlgCat.Over.Etale.diagram R K) where
  pt := sourceObject (R := R) (p := p) (Rsh := Rsh)
  ι :=
    { app := fun A => sourceMap (hbase := hbase) coordinate presentation A
      naturality := fun {A B} f =>
        sourceMap_naturality (hbase := hbase) coordinate presentation
          (A := A) (B := B) f }

/-- The source pointed-etale cocone admits a colimit witness.  As with the
localized presentation, the witness is stated propositionally rather than
manufactured as deferred non-Prop data. -/
@[stacks 04GW "source pointed-etale strict-henselization colimit"]
theorem sourceIsColimit
    (presentation : Presentation (hbase := hbase) coordinate) :
    Nonempty (IsColimit (sourceCocone (hbase := hbase) coordinate presentation)) := sorry

end Presentation

/-- Existence of presentation data is stated propositionally; the shared layer
does not manufacture a public non-Prop witness from Classical.choose. -/
@[stacks 04GW "existence of a pointed-etale strict-henselization presentation"]
theorem exists_presentation
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) :
    Nonempty (Presentation (hbase := hbase) coordinate) := sorry

end

end IsStrictHenselizationOf.PointedEtale
