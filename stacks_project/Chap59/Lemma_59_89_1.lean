/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap58.Lemma_58_5_2
public import stacks_project.Chap59.Theorem_59_82_7_Gabber_Restrict
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Compatibility of a base-changed rational point with the defining cospan of
`X_{k'}`. -/
theorem rationalPointBaseChange_lift_condition
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    (FieldExtension.specMap k k' ≫
          inv (SchemeOverField.point k).hom ≫ x.left) ≫ X.hom =
      𝟙 (Spec (CommRingCat.of k')) ≫ FieldExtension.specMap k k' :=
  sorry

/-- The `k'`-point `x_{k'}` of the field-extension base change `X_{k'}`, as a morphism
from `Spec k'`. -/
noncomputable def rationalPointBaseChange
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    Spec (CommRingCat.of k') ⟶ (FieldExtension.Over.baseChange k k' X).left :=
  pullback.lift
    (FieldExtension.specMap k k' ≫ inv (SchemeOverField.point k).hom ≫ x.left)
    (𝟙 (Spec (CommRingCat.of k')))
    (rationalPointBaseChange_lift_condition x)

/-- The base-changed point is a section of `X_{k'} ⟶ Spec k'`. -/
theorem rationalPointBaseChange_comp_hom
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    rationalPointBaseChange x ≫ (FieldExtension.Over.baseChange k k' X).hom =
      𝟙 (Spec (CommRingCat.of k')) :=
  sorry

/-- Projecting `x_{k'}` back to `X` recovers the composite of `x` with `Spec k' ⟶ Spec k`. -/
theorem rationalPointBaseChange_comp_toSource
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    rationalPointBaseChange x ≫ FieldExtension.toSource k k' X.hom =
      FieldExtension.specMap k k' ≫ inv (SchemeOverField.point k).hom ≫ x.left :=
  sorry

/-- A finite étale cover of a scheme over a field is split over a given rational point if the
point lifts through the cover. -/
def IsSplitOver {k : Type u} [Field k] {X : Scheme.{u}}
    (Z : Scheme.FiniteEtale X) (p : Spec (CommRingCat.of k) ⟶ X) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ Z.left, s ≫ Z.hom = p

/-- Unfolding of `IsSplitOver` as the existence of a section through the cover. -/
theorem IsSplitOver.iff {k : Type u} [Field k] {X : Scheme.{u}}
    (Z : Scheme.FiniteEtale X) (p : Spec (CommRingCat.of k) ⟶ X) :
    IsSplitOver Z p ↔ ∃ s : Spec (CommRingCat.of k) ⟶ Z.left, s ≫ Z.hom = p :=
  sorry

/-- The two legs of the comparison `Z_{K'} ⟶ X_K` agree over `Spec k`. -/
theorem galoisCoverToBaseChange_commutes
    {k k' : Type u} (K K' : Type u)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k' K'] [Algebra K K']
    [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (X : SchemeOverField k)
    (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left) :
    (FieldExtension.toSource k' K'
          (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
        Z.hom ≫ FieldExtension.toSource k k' X.hom) ≫ X.hom =
      (FieldExtension.toBase k' K'
          (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
        FieldExtension.specMap K K') ≫ FieldExtension.specMap k K :=
  sorry

/-- The comparison morphism `Z_{K'} ⟶ X_K` induced by a finite étale cover of `X_{k'}`
after extending scalars along `k' ⊂ K'` and `K ⊂ K'`. -/
noncomputable def galoisCoverToBaseChange
    {k k' : Type u} (K K' : Type u)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k' K'] [Algebra K K']
    [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (X : SchemeOverField k)
    (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left) :
    FieldExtension.baseChange k' K'
        (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ⟶
      (FieldExtension.Over.baseChange k K X).left :=
  pullback.lift
    (FieldExtension.toSource k' K'
        (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
      Z.hom ≫ FieldExtension.toSource k k' X.hom)
    (FieldExtension.toBase k' K'
        (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
      FieldExtension.specMap K K')
    (galoisCoverToBaseChange_commutes K K' X Z)

/-- The comparison `Z_{K'} ⟶ X_K` projects to `X` as the composite through `Z` and `X_{k'}`. -/
theorem galoisCoverToBaseChange_comp_toSource
    {k k' : Type u} (K K' : Type u)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k' K'] [Algebra K K']
    [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (X : SchemeOverField k)
    (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left) :
    galoisCoverToBaseChange K K' X Z ≫ FieldExtension.toSource k K X.hom =
      FieldExtension.toSource k' K'
          (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
        Z.hom ≫ FieldExtension.toSource k k' X.hom :=
  sorry

/-- The comparison `Z_{K'} ⟶ X_K` projects to `Spec K` as `Z_{K'} ⟶ Spec K' ⟶ Spec K`. -/
theorem galoisCoverToBaseChange_comp_toBase
    {k k' : Type u} (K K' : Type u)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k' K'] [Algebra K K']
    [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (X : SchemeOverField k)
    (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left) :
    galoisCoverToBaseChange K K' X Z ≫ FieldExtension.toBase k K X.hom =
      FieldExtension.toBase k' K'
          (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
        FieldExtension.specMap K K' :=
  sorry

/-- Lemma 59.89.1: for a field extension `K / k`, a smooth affine curve `X` over `k` with a
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
    [∀ (A B : Scheme.{u}) (i : B ⟶ A), (etaleAbelianRestriction i).Additive]
    [∀ (A B : Scheme.{u}) (i : B ⟶ A), (etaleAbelianRestriction i).PreservesHomology]
    [∀ (A B : Scheme.{u}) (i : B ⟶ A),
      (etaleAbelianRestriction i).PreservesInjectiveObjects]
    [∀ (A B : Scheme.{u}) (i : B ⟶ A),
      (etaleAbelianRestriction i ⋙
        siteAbelianSectionsFunctor B.smallEtaleTopology (terminal B.Etale)).Additive]
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
        IsSplitOver Z (rationalPointBaseChange x) ∧
          (CategoryTheory.forget AddCommGrpCat).map
              (etaleCohomologyRestrict (galoisCoverToBaseChange K K' X Z)
                ((etaleAbelianRestriction
                    (FieldExtension.Over.baseChange k K X).hom).obj F) q)
              ξ = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Etale

