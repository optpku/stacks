/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Henselian
public import stacks_project.Chap59.Lemma_59_82_6
public import stacks_project.Chap59.Theorem_59_82_7_Gabber_Restrict
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Theorem 59.82.7 (Gabber). Let `(A, I)` be a henselian pair. Set
`X = Spec A` and `Z = Spec (A ⧸ I)`. For any torsion abelian sheaf `F` on
`X_étale` the restriction morphism
`etaleCohomologyRestrict (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q`
is an isomorphism
`etaleCohomology X F q ≅ etaleCohomology Z (F|_Z) q` for every `q`. -/
@[stacks 09ZI]
theorem etaleCohomologyRestrict_isIso_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    [HasSheafify (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (Spec (CommRingCat.of A)).Etale]
    [(siteAbelianSectionsFunctor (Spec (CommRingCat.of A)).smallEtaleTopology
        (terminal (Spec (CommRingCat.of A)).Etale)).Additive]
    [HasSheafify (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (Spec (CommRingCat.of (A ⧸ I))).Etale]
    [(siteAbelianSectionsFunctor (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology
        (terminal (Spec (CommRingCat.of (A ⧸ I))).Etale)).Additive]
    [((smallEtalePullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).sheafPushforwardContinuous
        AddCommGrpCat.{u}
        (Spec (CommRingCat.of A)).smallEtaleTopology
        (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology).IsRightAdjoint]
    [(etaleAbelianRestriction
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Additive]
    [(etaleAbelianRestriction
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).PreservesHomology]
    [(etaleAbelianRestriction
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).PreservesInjectiveObjects]
    [(etaleAbelianRestriction
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⋙
        siteAbelianSectionsFunctor (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology
          (terminal (Spec (CommRingCat.of (A ⧸ I))).Etale)).Additive]
    (F : Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})
    (hF : Sheaf.IsLocallyTorsion F) (q : ℕ) :
    IsIso (etaleCohomologyRestrict
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
