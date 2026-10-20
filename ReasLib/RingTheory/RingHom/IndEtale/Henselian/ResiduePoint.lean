module

public import ReasLib.RingTheory.RingHom.IndEtale.Henselian
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ideal presentations of ind-etale residue-point lifts

The canonical lifting owner is `RingHom.IndEtale.existsUnique_lift`, whose
point is a `PrimeSpectrum` object and whose conclusion uses
`RingHom.IsResidueLift`.  This leaf keeps the useful ideal/residue-map view as
a neutral bridge for callers that already have a prime ideal and its residue
field map.  Its primary ideal statements use `RingHom.IndEtale`; explicit
`_ofRaw` companions retain arbitrary filtered-presentation universes.  It
does not introduce a second lifting principle.

@stack 08HR
-/

open IsLocalRing

universe u v w x y

namespace RingHom.IndEtale.ResiduePoint

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S]

/-- Lemma 10.154.6 (tag `08HR`) in ideal form: an ind-etale algebra has a
unique lift to a Henselian local target inducing a prescribed residue-point
map. -/
@[stacks 08HR "ind-etale ideal residue-point lift"]
theorem existsUnique_lift_ofIdeal
    (hA : (algebraMap R A).IndEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R).comp f =
        RingHom.ResiduePoint.of (R := R) q (maximalIdeal S) hq τ hτ := sorry

/-- The arbitrary-presentation-universe companion to
`existsUnique_lift_ofIdeal`. -/
@[stacks 08HR "ind-etale ideal residue-point lift from a raw presentation"]
theorem existsUnique_lift_ofIdeal_ofRaw
    (hA : RingHom.IndEtale.Raw.{u, v, x} (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R).comp f =
        RingHom.ResiduePoint.of (R := R) q (maximalIdeal S) hq τ hτ := sorry

/-- The same ideal lift with the residue-map equality unpacked into the
contracted-prime and induced-map clauses. -/
@[stacks 08HR "ind-etale ideal residue-map lift"]
theorem existsUnique_lift_ofIdeal_residueMap
    (hA : (algebraMap R A).IndEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := sorry

/-- The arbitrary-presentation-universe companion to
`existsUnique_lift_ofIdeal_residueMap`. -/
@[stacks 08HR "ind-etale ideal residue-map lift from a raw presentation"]
theorem existsUnique_lift_ofIdeal_residueMap_ofRaw
    (hA : RingHom.IndEtale.Raw.{u, v, x} (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := sorry

/-- A bijective canonical map from the residue field of `q.under R` to the
residue field of `q` determines the target residue map and hence a unique
ind-etale lift.  This is the neutral adapter for source statements that name
only the selected prime and a residue-field bijectivity hypothesis. -/
@[stacks 04GR "ind-etale ideal lift from residue-field bijectivity"]
theorem existsUnique_lift_ofIdeal_ofBijective
    (hA : (algebraMap R A).IndEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (hκ : Function.Bijective
      (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq =
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S)
            (algebraMap R S) hq).comp
            (RingEquiv.ofBijective
              (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) hκ).symm.toRingHom := sorry

/-- The arbitrary-presentation-universe companion to
`existsUnique_lift_ofIdeal_ofBijective`. -/
@[stacks 04GR "ind-etale ideal lift from residue-field bijectivity and a raw presentation"]
theorem existsUnique_lift_ofIdeal_ofBijective_ofRaw
    (hA : RingHom.IndEtale.Raw.{u, v, x} (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (hκ : Function.Bijective
      (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq =
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S)
            (algebraMap R S) hq).comp
            (RingEquiv.ofBijective
              (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) hκ).symm.toRingHom := sorry

/-- If the source residue map is bijective, the residue-coordinate condition in the ind-etale
lifting theorem is forced.  Thus the lift is uniquely characterized by the inverse image of the
closed point alone. -/
@[stacks 04GR "ind-etale ideal lift characterized by the inverse-image prime"]
theorem existsUnique_lift_ofIdeal_comap_ofBijective
    (hA : (algebraMap R A).IndEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (hκ : Function.Bijective
      (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)) :
    ∃! f : A →ₐ[R] S,
      q = Ideal.comap (f : A →+* S) (maximalIdeal S) := sorry

/-- The arbitrary-presentation-universe companion to
`existsUnique_lift_ofIdeal_comap_ofBijective`. -/
@[stacks 04GR "inverse-image characterization from a raw ind-etale presentation"]
theorem existsUnique_lift_ofIdeal_comap_ofBijective_ofRaw
    (hA : RingHom.IndEtale.Raw.{u, v, x} (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (hκ : Function.Bijective
      (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)) :
    ∃! f : A →ₐ[R] S,
      q = Ideal.comap (f : A →+* S) (maximalIdeal S) := sorry

/-- An external residue-field coordinate can be used directly in the ideal lifting API.  The
equivalence `e` transports the target ideal residue field to `K`; the compatibility hypothesis is
therefore stated entirely in the external coordinates, while the conclusion records the same
coordinate equality for the unique lift. -/
@[stacks 08HR "ind-etale ideal lift in external residue coordinates"]
theorem existsUnique_lift_ofIdeal_residueEquiv
    {K : Type y} [NonAssocSemiring K]
    (hA : (algebraMap R A).IndEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (e : (maximalIdeal S).ResidueField ≃+* K)
    (τ : q.ResidueField →+* K)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        e.toRingHom.comp
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        e.toRingHom.comp (Ideal.ResidueField.map q (maximalIdeal S)
          (f : A →+* S) hfq) = τ := sorry

/-- The arbitrary-presentation-universe companion to
`existsUnique_lift_ofIdeal_residueEquiv`. -/
@[stacks 08HR "ind-etale ideal lift in external residue coordinates from a raw presentation"]
theorem existsUnique_lift_ofIdeal_residueEquiv_ofRaw
    {K : Type y} [NonAssocSemiring K]
    (hA : RingHom.IndEtale.Raw.{u, v, x} (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (e : (maximalIdeal S).ResidueField ≃+* K)
    (τ : q.ResidueField →+* K)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        e.toRingHom.comp
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        e.toRingHom.comp (Ideal.ResidueField.map q (maximalIdeal S)
          (f : A →+* S) hfq) = τ := sorry

end RingHom.IndEtale.ResiduePoint
