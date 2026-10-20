module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.HenselianPair
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Theorem 59.82.7 (Gabber). Let `(A, I)` be a henselian pair. Set
`X = Spec A` and `Z = Spec (A ⧸ I)`. For any torsion abelian sheaf `F` on
`X_étale` the restriction morphism
`etaleCohomologyRestrict (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q`
is an isomorphism
`etaleCohomology X F q ≅ etaleCohomology Z (F|_Z) q` for every `q`. -/
@[stacks 09ZI] #check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomologyRestrict_isIso_of_henselianPair :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
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
    (F : Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})
    (hF : Sheaf.IsLocallyTorsion F) (q : ℕ),
    IsIso (etaleCohomologyRestrict
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q))

end AlgebraicGeometry.Scheme.Etale
