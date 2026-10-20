/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.RationalPoint
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.PointedBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a field extension `K / k`, a smooth affine curve `X` over `k` with a
rational point `x`, and an abelian étale sheaf `F` on `Spec K` annihilated by an integer `n`
invertible in `k`, every positive-degree class
`ξ ∈ H^q(X_K, (X_K ⟶ Spec K)⁻¹ F)` dies after a finite extension tower `k' / k ⊂ K' / K`
and a finite étale Galois cover `Z ⟶ X_{k'}` whose group order divides a power of `n` and
which splits over `x_{k'}`. -/
@[stacks 0EYT]
theorem exists_finiteEtaleGalois_etaleCohomologyRestrict_eq_zero
    {k K : Type u} [Field k] [Field K] [Algebra k K]
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
            (FieldExtension.Over.baseChange k K X).hom).obj F) q)) :
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
              ξ = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Etale
