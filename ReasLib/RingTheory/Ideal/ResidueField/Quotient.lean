module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prime residue fields of quotient rings

This leaf owns the comparison between the residue field of a prime ideal and
the residue field of the zero ideal in its quotient.  The construction only
uses a commutative base algebra and primality, so it belongs to `Ideal` rather
than to the local-ring quotient layer.

@stack 051P
-/

namespace Ideal.ResidueField

universe u v

/-- Lemma 10.115.6, tag 051P: the residue field of a prime ideal is canonically
algebra-equivalent to the residue field of the zero ideal in its quotient ring. -/
@[stacks 051P]
noncomputable def quotientBotAlgEquiv
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
    (I : Ideal A) [I.IsPrime] :
    I.ResidueField ≃ₐ[K] ((⊥ : Ideal (A ⧸ I)).ResidueField) :=
  let hcomap : I = Ideal.comap (Ideal.Quotient.mkₐ K I) ⊥ :=
    (Ideal.mk_ker (I := I)).symm.trans
      (RingHom.ker_eq_comap_bot (Ideal.Quotient.mkₐ K I))
  AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ I ⊥ (Ideal.Quotient.mkₐ K I) hcomap)
    (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (f := (Ideal.Quotient.mk I : A →+* A ⧸ I))
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
      I ⊥ hcomap)

/-- The quotient residue-field equivalence has the canonical residue-field
map induced by `A → A ⧸ I` as its underlying function. -/
@[simp, stacks 051P "prime quotient residue-field equivalence computation"]
theorem quotientBotAlgEquiv_apply
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
    (I : Ideal A) [I.IsPrime] (x : I.ResidueField) :
    quotientBotAlgEquiv (K := K) I x =
      Ideal.ResidueField.mapₐ I ⊥ (Ideal.Quotient.mkₐ K I)
        ((Ideal.mk_ker (I := I)).symm.trans
          (RingHom.ker_eq_comap_bot (Ideal.Quotient.mkₐ K I))) x := sorry

/-- Lemma 10.115.6, tag 051P: the residue field of a prime ideal and its
prime quotient have the same transcendence degree over every commutative base algebra. -/
@[stacks 051P]
theorem trdeg_eq_quotient
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
    (I : Ideal A) [I.IsPrime] :
    Algebra.trdeg K I.ResidueField = Algebra.trdeg K (A ⧸ I) := sorry

/-- Lemma 10.115.6, tag 051P: the natural-number view of the transcendence degree of a
prime residue field agrees with that of the corresponding prime quotient. -/
@[stacks 051P]
theorem trdegToNat_eq_quotient
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
    (I : Ideal A) [I.IsPrime] :
    Cardinal.toNat (Algebra.trdeg K I.ResidueField) =
      Cardinal.toNat (Algebra.trdeg K (A ⧸ I)) := sorry

end Ideal.ResidueField
