/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Polynomial.Local
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

@[expose] public section

/-!
# Local `AdjoinRoot` algebras

This leaf records the local-ring consequences of an irreducible polynomial
after reduction to the residue field.  The reduction itself is owned by
`Polynomial.Local`; this namespace only supplies the quotient, locality, and
residue-field bridges for `AdjoinRoot`.
-/

universe u

namespace AdjoinRoot.Local

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The quotient of a monogenic algebra by the extended maximal ideal is the
monogenic algebra defined by the reduced polynomial. -/
noncomputable def quotientEquiv (f : Polynomial A) :
    (AdjoinRoot f ⧸ Ideal.map (algebraMap A (AdjoinRoot f))
        (IsLocalRing.maximalIdeal A)) ≃+*
      AdjoinRoot (Polynomial.Local.reduction f) := by
  change
    (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal A)) ≃+*
      AdjoinRoot (Polynomial.map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) f)
  exact (AdjoinRoot.quotEquivQuotMap f (IsLocalRing.maximalIdeal A)).toRingEquiv

/-- A monic polynomial whose residue-field reduction is irreducible defines a
local `AdjoinRoot` algebra. -/
theorem isLocalRing (f : Polynomial A) (hf : f.Monic)
    (hred : Irreducible (Polynomial.Local.reduction f)) :
    IsLocalRing (AdjoinRoot f) := sorry

/-- The extended maximal ideal of a local `AdjoinRoot` algebra is its
maximal ideal when the reduced polynomial is irreducible. -/
theorem mapsMaximalIdeal (f : Polynomial A)
    (hred : Irreducible (Polynomial.Local.reduction f))
    [IsLocalRing (AdjoinRoot f)] :
    RingHom.MapsMaximalIdeal (algebraMap A (AdjoinRoot f)) := sorry

/-- The residue field of a local `AdjoinRoot` algebra is the monogenic algebra
defined by the reduced polynomial. -/
noncomputable def residueFieldEquiv (f : Polynomial A)
    (hred : Irreducible (Polynomial.Local.reduction f))
    [IsLocalRing (AdjoinRoot f)] :
    IsLocalRing.ResidueField (AdjoinRoot f) ≃+*
      AdjoinRoot (Polynomial.Local.reduction f) := by
  letI : Fact (Irreducible (Polynomial.Local.reduction f)) := Fact.mk hred
  let J : Ideal (AdjoinRoot f) :=
    Ideal.map (algebraMap A (AdjoinRoot f)) (IsLocalRing.maximalIdeal A)
  let e :
      (AdjoinRoot f ⧸ J) ≃+* AdjoinRoot (Polynomial.Local.reduction f) :=
    quotientEquiv f
  have hqf : IsField (AdjoinRoot f ⧸ J) := by
    exact e.isField (Field.toIsField (AdjoinRoot (Polynomial.Local.reduction f)))
  have hJmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hqf
  have hJ :
      Ideal.map (algebraMap A (AdjoinRoot f)) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal (AdjoinRoot f) :=
    by simpa [J] using IsLocalRing.eq_maximalIdeal hJmax
  have hJ_of :
      Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal (AdjoinRoot f) := by
    simpa [AdjoinRoot.algebraMap_eq] using hJ
  change
    (AdjoinRoot f ⧸ IsLocalRing.maximalIdeal (AdjoinRoot f)) ≃+*
      AdjoinRoot (Polynomial.Local.reduction f)
  exact (Ideal.quotEquivOfEq hJ_of).symm.trans (quotientEquiv f)

/-- The residue-field equivalence sends the residue map of the coefficient
ring to the canonical coefficient map into the reduced `AdjoinRoot`. -/
theorem residueFieldEquiv_comp_residueFieldMap (f : Polynomial A)
    (hred : Irreducible (Polynomial.Local.reduction f))
    [IsLocalRing (AdjoinRoot f)]
    [IsLocalHom (algebraMap A (AdjoinRoot f))] :
    (residueFieldEquiv f hred).toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap A (AdjoinRoot f))) =
      algebraMap (IsLocalRing.ResidueField A)
        (AdjoinRoot (Polynomial.Local.reduction f)) := sorry

end AdjoinRoot.Local
