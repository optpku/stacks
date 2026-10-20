module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Presentation.Jacobian.Cotangent

@[expose] public section

open CategoryTheory
open scoped DerivedExt

universe u v

namespace Algebra.Presentation

/- Lemma 88.7.1 (1): for a presentation `P` of `B` over `A` on `n` variables and
`m` relations with `m ≤ n`, the image in `B` of the leading `m × m` Jacobian
determinant annihilates `Ext¹_B(NL{B⁄A}, N)` for every `B`-module `N`. -/
@[stacks 0GAV] #check
  (Algebra.Presentation.leadingJacobianDet_annihilates_extOne_naiveCotangent :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      {n m : ℕ} (P : Presentation A B (Fin n) (Fin m)) (hmn : m ≤ n),
      twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject A B)
        (Ideal.span {algebraMap P.Ring B (P.leadingJacobianDet hmn le_rfl)}))

/- Lemma 88.7.1 (2): if `n = m`, then multiplication by the leading Jacobian
determinant is zero on `NL{B⁄A}` in `D(B)`. -/
@[stacks 0GAV] #check
  (Algebra.Presentation.leadingJacobianDet_smul_id_naiveCotangentObject_eq_zero :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      {n : ℕ} (P : Presentation A B (Fin n) (Fin n)),
      algebraMap P.Ring B (P.leadingJacobianDet le_rfl le_rfl) •
        𝟙 (naiveCotangentObject A B) = 0)

end Algebra.Presentation
