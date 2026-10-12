/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps to dominating valuation subrings

This leaf packages two canonical domination interfaces: the codomain restriction of a map into a
field when its local range is contained in a valuation subring, and the valuation subring induced
by a discrete valuation ring in its fraction field.  The constructions are independent of affine
blowups and provide the reusable interfaces for domination arguments.
-/

@[expose] public section

universe u v w

namespace ValuationSubring

variable {R : Type u} {K : Type v} [CommRing R] [Field K]

section Dvr

variable {A : Type w} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Algebra A K] [IsFractionRing A K]

/-- The valuation subring of a fraction field canonically induced by a discrete valuation ring.

The construction uses the adic valuation of the maximal ideal of `A`; it is deliberately exposed
as a named datum so downstream arguments can share the same fraction-field model. -/
@[stacks 00PH "valuation subring induced by a discrete valuation ring"]
noncomputable def ofDvr : ValuationSubring K :=
  ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring

/-- The canonical `ofDvr` construction is again a discrete valuation ring. -/
@[stacks 00PH "discrete valuation ring of the induced valuation subring"]
theorem ofDvr_isDiscreteValuationRing :
    IsDiscreteValuationRing (ofDvr (A := A) (K := K)) := sorry

/-- The canonical local subring of `ofDvr` is exactly the image of `A` in its fraction field. -/
@[stacks 00PH "range characterization of the induced valuation subring"]
theorem ofDvr_toLocalSubring_eq_range :
    (ofDvr (A := A) (K := K)).toLocalSubring =
      LocalSubring.range (algebraMap A K) := sorry

end Dvr

section DvrDomination

variable {A : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [IsFractionRing A L]

/-- A local map into a discrete valuation ring is dominated by its canonical valuation subring in
the common fraction field.  The ring-hom form is the reusable core; algebra-map specializations
should use this bridge rather than reconstructing the valuation witness. -/
@[stacks 00PH "domination by the valuation subring of a discrete valuation ring"]
theorem ofDvr_dominates
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R →+* A) [IsLocalHom f] :
    LocalSubring.range ((algebraMap A L).comp f) ≤
      (ofDvr (A := A) (K := L)).toLocalSubring := sorry

/-- Package the canonical DVR-induced valuation subring as an existential domination witness. -/
@[stacks 00PH "existence of a valuation subring dominating a local DVR map"]
theorem exists_ofDvr_dominating
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R →+* A) [IsLocalHom f] :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range ((algebraMap A L).comp f) ≤ V.toLocalSubring := sorry

end DvrDomination

variable [IsLocalRing R]

/-- Regard a map to a field as a map to a valuation subring containing its local range. -/
@[stacks 052M "map to a dominating valuation subring"]
def mapOfRangeLe
    (f : R →+* K) (A : ValuationSubring K)
    (hA : LocalSubring.range f ≤ A.toLocalSubring) : R →+* A :=
  f.codRestrict A.toSubring
    (fun r => hA.1 (show f r ∈ (LocalSubring.range f).toSubring from ⟨r, rfl⟩))

/-- The underlying map of `ValuationSubring.mapOfRangeLe` is the original map to the field. -/
@[stacks 052M "underlying map to a dominating valuation subring", simp]
theorem coe_mapOfRangeLe
    (f : R →+* K) (A : ValuationSubring K)
    (hA : LocalSubring.range f ≤ A.toLocalSubring) (r : R) :
    (mapOfRangeLe f A hA r : K) = f r := sorry

section Local

variable [IsLocalRing R]

/-- The map to a dominating valuation subring is local. -/
@[stacks 052M "local map to a dominating valuation subring"]
theorem isLocalHom_mapOfRangeLe
    (f : R →+* K) (A : ValuationSubring K)
    (hA : LocalSubring.range f ≤ A.toLocalSubring) :
    IsLocalHom (mapOfRangeLe f A hA) := sorry

end Local

section Algebra

variable [Algebra R K]

/-- The canonical algebra map with codomain restricted to a dominating valuation subring. -/
@[stacks 052M "algebra map to a dominating valuation subring"]
def algebraMapOfRangeLe
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) : R →+* A :=
  mapOfRangeLe (algebraMap R K) A hA

/-- View a valuation subring containing the image of `R` as an `R`-subalgebra of the field. -/
@[stacks 052M "dominating valuation subring as a subalgebra"]
def subalgebraOfRangeLe
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) : Subalgebra R K where
  __ := A.toSubring
  algebraMap_mem' := fun r =>
    hA.1 (show algebraMap R K r ∈ (LocalSubring.range (algebraMap R K)).toSubring from ⟨r, rfl⟩)

/-- The underlying field-valued map of `ValuationSubring.algebraMapOfRangeLe` is `algebraMap`. -/
@[stacks 052M "underlying algebra map to a dominating valuation subring", simp]
theorem coe_algebraMapOfRangeLe
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) (r : R) :
    (algebraMapOfRangeLe A hA r : K) = algebraMap R K r := sorry

variable [IsLocalRing R]

/-- The canonical algebra map to a dominating valuation subring is local. -/
@[stacks 052M "local algebra map to a dominating valuation subring"]
theorem isLocalHom_algebraMapOfRangeLe
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) :
    IsLocalHom (algebraMapOfRangeLe A hA) := sorry

/-- The algebra map to a dominating valuation subring, viewed as a subalgebra of the field, is
local. -/
@[stacks 052M "local algebra map to a dominating valuation subring subalgebra"]
theorem isLocalHom_algebraMap_subalgebraOfRangeLe
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) :
    IsLocalHom (algebraMap R (subalgebraOfRangeLe A hA)) := sorry

end Algebra

end ValuationSubring

namespace LocalSubring

variable {R : Type u} {A : Type v} {L : Type w}
variable [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
variable [CommRing L] [Nontrivial L]

/-- The local range of a composite is dominated by the local range of its second map when the
first map is local. -/
@[stacks 00PH "local-hom range domination under composition"]
theorem range_comp_le_range_of_isLocalHom
    (f : R →+* A) (g : A →+* L) [IsLocalHom f] :
    range (g.comp f) ≤ range g := sorry

variable [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]

/-- A local algebra map makes the local range of the composite algebra map dominated by the
local range of the upper algebra map. -/
@[stacks 00PH "local algebra-map range domination"]
theorem range_algebraMap_le_of_isLocalHom [IsLocalHom (algebraMap R A)] :
    range (algebraMap R L) ≤ range (algebraMap A L) := sorry

end LocalSubring
