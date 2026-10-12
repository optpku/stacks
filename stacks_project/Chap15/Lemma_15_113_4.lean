/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Lemma 15.113.4

@stack 09ED
-/

@[expose] public section

open Ideal IsLocalRing
open scoped Pointwise

universe u v w

/-
Lemma 15.113.4 (tag 09ED): Let `A` be a discrete valuation ring with fraction
field `K` and residue field `κ`, let `L/K` be finite Galois, and let
`B = integralClosure A L`.  For a maximal ideal `m` of `B`, the extension
`κ(m) / κ` is normal and the decomposition-group map is surjective.  The
separability condition is independent of the chosen maximal ideal; when it
holds, the extension is Galois and the same map is surjective onto its Galois
group.

The four checks below split the source's independent mathematical clauses.
The reusable normality, stabilizer, orbit-separability, and Galois bridges are
owned by `integralClosure.ResidueField`.
-/

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
variable [IsScalarTower A K L] [IsGalois K L] [FiniteDimensional K L]

/- Lemma 15.113.4 (1): normality of the residue-field extension. -/
@[stacks 09ED "Lemma 15.113.4 (1)"]
#check fun (m : Ideal (integralClosure A L)) [m.IsMaximal] ↦
  (integralClosure.ResidueField.normal (K := K) (maximalIdeal A) m :
    letI : Algebra (maximalIdeal A).ResidueField m.ResidueField :=
      integralClosure.ResidueField.algebraOfBase m
    Normal (maximalIdeal A).ResidueField m.ResidueField)

/- Lemma 15.113.4 (2) and (4): the decomposition-group map is onto the residue-field
automorphism group.  Under the source's separability hypothesis this is the stated map onto the
Galois group, so the same stronger canonical theorem covers both numbered clauses. -/
@[stacks 09ED "Lemma 15.113.4 (2) and (4)"]
#check fun (m : Ideal (integralClosure A L)) [m.IsMaximal] ↦
  (integralClosure.ResidueField.stabilizerHom_surjective (K := K)
    (maximalIdeal A) m :
    Function.Surjective
      (Ideal.ResidueField.Invariant.stabilizerHom
        (G := Gal(L/K)) (maximalIdeal A) m))

/- Lemma 15.113.4, separability hypothesis: separability for one maximal ideal is equivalent to
separability for every maximal ideal.  The reusable owner only needs equality
of the two contractions; maximality supplies that equality here. -/
@[stacks 09ED "Lemma 15.113.4, separability hypothesis"]
#check fun (m m' : Ideal (integralClosure A L)) [m.IsMaximal] [m'.IsMaximal] ↦
  integralClosure.ResidueField.isSeparable_iff_of_under_eq (K := K) m m'
    ((Ideal.LiesOver.over (P := m) (p := maximalIdeal A)).symm.trans
      (Ideal.LiesOver.over (P := m') (p := maximalIdeal A)))

/- Lemma 15.113.4 (3): a separable residue-field extension is Galois. -/
@[stacks 09ED "Lemma 15.113.4 (3)"]
#check fun (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hsep :
      letI : Algebra (maximalIdeal A).ResidueField m.ResidueField :=
        integralClosure.ResidueField.algebraOfBase m
      Algebra.IsSeparable (maximalIdeal A).ResidueField m.ResidueField) ↦
  (integralClosure.ResidueField.isGalois_of_separable (K := K)
    (maximalIdeal A) m hsep :
    letI : Algebra (maximalIdeal A).ResidueField m.ResidueField :=
      integralClosure.ResidueField.algebraOfBase m
    IsGalois (maximalIdeal A).ResidueField m.ResidueField)

end
