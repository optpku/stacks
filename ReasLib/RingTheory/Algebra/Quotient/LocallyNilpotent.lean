module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import ReasLib.RingTheory.Ideal.LocallyNilpotent

/-!
# Surjectivity Across Locally Nilpotent Base-Ideal Quotients

This leaf gives the map-level lifting theorem for a finite-type target after
quotienting source and target by the extensions of a locally nilpotent base
ideal.  The quotient map itself is owned by `AlgHom.quotientByBaseIdeal`.
-/

@[expose] public section

universe u v w

namespace AlgHom.BaseIdeal

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- Tag `07RD`: a map into a finite-type algebra is surjective when the map
induced after quotienting by a locally nilpotent base ideal is surjective. -/
@[stacks 07RD "surjectivity across a locally nilpotent base-ideal quotient"]
theorem surjective_of_quotient_surjective
    (f : A →ₐ[R] B) (I : Ideal R) [Algebra.FiniteType R B]
    (hI : I.IsLocallyNilpotent)
    (hquot : Function.Surjective (f.quotientByBaseIdeal I)) :
    Function.Surjective f := sorry

/-- Tag `07RD`: the same lifting theorem with the original-base quotient map
as input.  This is the map-level consumer API; use
`quotientMap_surjective_iff` when the quotient-base view is already available. -/
@[stacks 07RD "surjectivity from the original-base quotient map"]
theorem surjective_of_quotientMap_surjective
    (f : A →ₐ[R] B) (I : Ideal R) [Algebra.FiniteType R B]
    (hI : I.IsLocallyNilpotent)
    (hquot : Function.Surjective (BaseIdeal.quotientMap f I)) :
    Function.Surjective f := sorry

/-- Lemma 10.126.9 (Tag 07RD): the raw target-quotient projection form of the
surjectivity lifting theorem.  This is the source-facing bridge to
`surjective_of_quotient_surjective`. -/
@[stacks 07RD "surjectivity from the raw base-ideal quotient projection"]
theorem surjective_of_quotient_mk_surjective
    (f : A →ₐ[R] B) (I : Ideal R) [Algebra.FiniteType R B]
    (hI : I.IsLocallyNilpotent)
    (hquot : Function.Surjective
      ((Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp f)) :
    Function.Surjective f := sorry

end AlgHom.BaseIdeal
