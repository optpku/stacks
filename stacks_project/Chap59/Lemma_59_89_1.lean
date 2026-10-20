module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.FiniteGaloisEffacement
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Lemma 59.89.1: Positive-degree étale cohomology classes on a pointed smooth affine curve
vanish after compatible finite field extensions and a finite étale Galois cover split at the
point, whose group order divides a power of the coefficient annihilator. -/
@[stacks 0EYT] #check (AlgebraicGeometry.Scheme.Etale.exists_finiteEtaleGalois_etaleCohomologyRestrict_eq_zero :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [SmoothOfRelativeDimension 1 X.hom] [IsAffine X.left]
    (x : SchemeOverField.point k ⟶ X) (n : ℕ) (hn : IsUnit (n : k))
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (hF : (n : ℤ) • 𝟙 F = 0) {q : ℕ} (hq : 0 < q)
    [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Y : Scheme.{u}, Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ Y : Scheme.{u},
      HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ Y : Scheme.{u}, HasTerminal Y.Etale]
    [∀ Y : Scheme.{u},
      (siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
    [∀ (A B : Scheme.{u}) (i : B ⟶ A),
      ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        A.smallEtaleTopology B.smallEtaleTopology).IsRightAdjoint]
    (ξ : (CategoryTheory.forget AddCommGrpCat).obj
      (etaleCohomology (FieldExtension.Over.baseChange k K X).left
        ((etaleAbelianRestriction
            (FieldExtension.Over.baseChange k K X).hom).obj F) q)),
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra k' K') (_ : Algebra k K')
      (_ : IsScalarTower k k' K') (_ : IsScalarTower k K K')
      (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left)
      (_ : GaloisCategory (Scheme.FiniteEtale
        (FieldExtension.Over.baseChange k k' X).left))
      (_ : IsGalois Z) (G : Type u) (_ : Group G) (_ : Finite G) (_ : Aut Z ≃* G)
      (m : ℕ),
      Nat.card G ∣ n ^ m ∧
        Scheme.FiniteEtale.IsSplitOver Z (FieldExtension.rationalPointBaseChange x) ∧
          (CategoryTheory.forget AddCommGrpCat).map
              (etaleCohomologyRestrict (Scheme.FiniteEtale.toBaseChange K K' X Z)
                ((etaleAbelianRestriction
                    (FieldExtension.Over.baseChange k K X).hom).obj F) q)
              ξ = 0)
