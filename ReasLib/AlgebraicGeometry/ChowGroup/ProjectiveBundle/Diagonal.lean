/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Tensor
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern
public import ReasLib.AlgebraicGeometry.Correspondence.Category
public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.TautologicalKernel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry BigOperators MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

variable {k : Type u} [Field k]

/-- The canonical map from the relative self-product of `P` over `X` to the product
of `P` with itself over the ground field. -/
def relativeProductMap {X P : SchemeOverField k} (p : P ⟶ X) :
    pullback p p ⟶ P ⨯ P :=
  prod.lift (pullback.fst p p) (pullback.snd p p)

/-- The relative-product comparison is the product lift of its two projections. -/
theorem relativeProductMap_def {X P : SchemeOverField k} (p : P ⟶ X) :
    relativeProductMap p = prod.lift (pullback.fst p p) (pullback.snd p p) := sorry

/-- The second projection of the relative-product comparison is the second pullback
projection. -/
theorem relativeProductMap_snd {X P : SchemeOverField k} (p : P ⟶ X) :
    relativeProductMap p ≫ (prod.snd : P ⨯ P ⟶ P) = pullback.snd p p := sorry

/-- The relative-product comparison is proper when the base is separated over the
ground field. -/
instance relativeProductMap_isProper {X P : SchemeOverField k} [IsSeparated X.hom]
    (p : P ⟶ X) : IsProper (relativeProductMap p).left := sorry

/-- The second projection of the relative self-product is flat for a represented
projective bundle. -/
theorem relativeProductSnd_flat (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] : Flat (pullback.snd p p).left := sorry

/-- The second projection of the relative self-product has relative dimension `q`
for a represented projective bundle of rank `q + 1`. -/
theorem relativeProductSnd_relativeDimension (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] :
    Scheme.Hom.RelativeDimension (pullback.snd p p).left q := sorry

/-- The relative self-product of two finite-type schemes over the ground field is
again locally of finite type over that field. -/
instance relativeProductLocallyOfFiniteType (X P : Correspondence.Category k)
    (p : P.scheme ⟶ X.scheme) : LocallyOfFiniteType (pullback p p).hom := sorry

/-- The pullback of the base diagonal to `P ⨯ P`, represented by flat pullback to
`P ×_X P` followed by proper pushforward. -/
noncomputable def baseDiagonalClass (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] :
    Correspondence.Integral P.scheme P.scheme (-(q : ℤ)) :=
  BivariantClass.properPushforward (fun _ ↦ 0) (relativeProductMap p) prod.snd (-(q : ℤ))
    ((relativeProductMap_snd p).symm ▸
      @BivariantClass.flatPullback _ inferInstance (fun _ ↦ 0) inferInstance
        _ _ inferInstance inferInstance (pullback.snd p p) q
        (relativeProductSnd_flat X P E p hp q)
        (relativeProductSnd_relativeDimension X P E p hp q))

/-- The base-diagonal class is proper pushforward of the flat-pullback class on the
relative self-product. -/
theorem baseDiagonalClass_def (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] :
    baseDiagonalClass X P E p hp q =
      BivariantClass.properPushforward (fun _ ↦ 0) (relativeProductMap p) prod.snd (-(q : ℤ))
        ((relativeProductMap_snd p).symm ▸
          @BivariantClass.flatPullback _ inferInstance (fun _ ↦ 0) inferInstance
            _ _ inferInstance inferInstance (pullback.snd p p) q
            (relativeProductSnd_flat X P E p hp q)
            (relativeProductSnd_relativeDimension X P E p hp q)) := sorry

/-- The `i`th homogeneous term in the top-Chern polynomial for the diagonal of a
projective bundle, using the top-degree tensor expansion of a rank-`q` module. -/
noncomputable def diagonalChernTerm (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] (i : Fin (q + 1)) :
    ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (P.scheme ⨯ P.scheme).hom q :=
  let hRank :
      Scheme.Modules.IsFiniteLocallyFreeOfRank q
        (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) :=
    Scheme.ProjectiveBundle.tautologicalKernel_isFiniteLocallyFreeOfRank p.left hp q
  let hK :
      (Scheme.ProjectiveBundle.tautologicalKernel p.left hp).IsFiniteLocallyFree :=
    @Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _
      q (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) hRank
  let hDual :
      (Scheme.Modules.dual
        (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)).IsFiniteLocallyFree :=
    @Scheme.Modules.IsFiniteLocallyFree.dual _
      (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) hK
  let hPull :
      ((Scheme.Modules.pullback
          (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
        (Scheme.Modules.dual
          (Scheme.ProjectiveBundle.tautologicalKernel p.left hp))).IsFiniteLocallyFree :=
    @Scheme.Modules.pullback_isFiniteLocallyFree _ _
      (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left
      (Scheme.Modules.dual (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)) hDual
  Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt) ▸
    ChowCohomology.Nonnegative.mul (fun _ ↦ 0) (P.scheme ⨯ P.scheme).hom
      (@ChernClass.chernClass _ _ inferInstance (fun _ ↦ 0) inferInstance
        (P.scheme ⨯ P.scheme).hom inferInstance
        ((Scheme.Modules.pullback
          (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
          (Scheme.Modules.dual
            (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)))
        hPull (q - i))
      (((nsmul_one (i : ℕ) : (i : ℕ) • (1 : ℤ) = (i : ℤ)) ▸
          GradedMonoid.GMonoid.gnpow i
            (@ChowCohomology.firstChernClass _ _ (fun _ ↦ 0)
              (P.scheme ⨯ P.scheme).hom inferInstance inferInstance inferInstance
              ((Scheme.Modules.pullback
                (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
                (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp))
              (Scheme.Modules.Invertible.pullback
                (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left
                (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p.left hp)))) :
        ChowCohomology.degree (fun _ ↦ 0) (P.scheme ⨯ P.scheme).hom (i : ℤ))

/-- A diagonal Chern term is the product of the two pulled-back homogeneous
Chern classes in the top-Chern expansion. -/
theorem diagonalChernTerm_def (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] (i : Fin (q + 1)) :
    diagonalChernTerm X P E p hp q i =
      let hRank :
          Scheme.Modules.IsFiniteLocallyFreeOfRank q
            (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) :=
        Scheme.ProjectiveBundle.tautologicalKernel_isFiniteLocallyFreeOfRank p.left hp q
      let hK :
          (Scheme.ProjectiveBundle.tautologicalKernel p.left hp).IsFiniteLocallyFree :=
        @Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _
          q (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) hRank
      let hDual :
          (Scheme.Modules.dual
            (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)).IsFiniteLocallyFree :=
        @Scheme.Modules.IsFiniteLocallyFree.dual _
          (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) hK
      let hPull :
          ((Scheme.Modules.pullback
              (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.Modules.dual
              (Scheme.ProjectiveBundle.tautologicalKernel p.left hp))).IsFiniteLocallyFree :=
        @Scheme.Modules.pullback_isFiniteLocallyFree _ _
          (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left
          (Scheme.Modules.dual (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)) hDual
      Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt) ▸
        ChowCohomology.Nonnegative.mul (fun _ ↦ 0) (P.scheme ⨯ P.scheme).hom
          (@ChernClass.chernClass _ _ inferInstance (fun _ ↦ 0) inferInstance
            (P.scheme ⨯ P.scheme).hom inferInstance
            ((Scheme.Modules.pullback
              (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
              (Scheme.Modules.dual
                (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)))
            hPull (q - i))
          (((nsmul_one (i : ℕ) : (i : ℕ) • (1 : ℤ) = (i : ℤ)) ▸
              GradedMonoid.GMonoid.gnpow i
                (@ChowCohomology.firstChernClass _ _ (fun _ ↦ 0)
                  (P.scheme ⨯ P.scheme).hom inferInstance inferInstance inferInstance
                  ((Scheme.Modules.pullback
                    (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
                    (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp))
                  (Scheme.Modules.Invertible.pullback
                    (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left
                    (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p.left hp)))) :
            ChowCohomology.degree (fun _ ↦ 0)
              (P.scheme ⨯ P.scheme).hom (i : ℤ)) := sorry

/-- The degree-`q` top-Chern polynomial occurring in the diagonal formula. -/
noncomputable def diagonalChernClass (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] :
    ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (P.scheme ⨯ P.scheme).hom q :=
  ∑ i : Fin (q + 1), diagonalChernTerm X P E p hp q i

/-- The diagonal Chern class is the complete finite sum indexed by `0, …, q`. -/
theorem diagonalChernClass_def (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] :
    diagonalChernClass X P E p hp q =
      ∑ i : Fin (q + 1), diagonalChernTerm X P E p hp q i := sorry

/-- The diagonal Chern polynomial is the degree-`q` Chern class of the tensor product
of the first pullback of the dual tautological kernel with the second pullback of the
tautological line module. -/
theorem diagonalChernClass_eq_topChern (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] :
    diagonalChernClass X P E p hp q =
      let hRank :
          Scheme.Modules.IsFiniteLocallyFreeOfRank q
            (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) :=
        Scheme.ProjectiveBundle.tautologicalKernel_isFiniteLocallyFreeOfRank p.left hp q
      let hK :
          (Scheme.ProjectiveBundle.tautologicalKernel p.left hp).IsFiniteLocallyFree :=
        @Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _
          q (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) hRank
      let hDual :
          (Scheme.Modules.dual
            (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)).IsFiniteLocallyFree :=
        @Scheme.Modules.IsFiniteLocallyFree.dual _
          (Scheme.ProjectiveBundle.tautologicalKernel p.left hp) hK
      let hPull :
          ((Scheme.Modules.pullback
              (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.Modules.dual
              (Scheme.ProjectiveBundle.tautologicalKernel p.left hp))).IsFiniteLocallyFree :=
        @Scheme.Modules.pullback_isFiniteLocallyFree _ _
          (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left
          (Scheme.Modules.dual (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)) hDual
      let _ :
          CategoryTheory.MonoidalCategory (P.scheme ⨯ P.scheme).left.Modules :=
        inferInstance
      let _ :
          Scheme.Modules.Invertible
            ((Scheme.Modules.pullback
              (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
              (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp)) :=
        Scheme.Modules.Invertible.pullback
          (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left
          (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p.left hp)
      let hLRank :
          ((Scheme.Modules.pullback
            (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp)).IsFiniteLocallyFreeOfRank 1 :=
        Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible
          ((Scheme.Modules.pullback
            (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp))
      let hL :
          ((Scheme.Modules.pullback
            (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp)).IsFiniteLocallyFree :=
        @Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _
          1
          ((Scheme.Modules.pullback
            (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp)) hLRank
      let hTensor :
          (((Scheme.Modules.pullback
                (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
              (Scheme.Modules.dual
                (Scheme.ProjectiveBundle.tautologicalKernel p.left hp))) ⊗
            (Scheme.Modules.pullback
              (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
                (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp)).IsFiniteLocallyFree :=
        @SheafOfModules.IsFiniteLocallyFree.tensor _ _ _ _ _ _ _ _ _
          ((Scheme.Modules.pullback
            (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.Modules.dual
              (Scheme.ProjectiveBundle.tautologicalKernel p.left hp)))
          ((Scheme.Modules.pullback
            (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp))
          hPull hL
      @ChernClass.chernClass _ _ inferInstance (fun _ ↦ 0) inferInstance
        (P.scheme ⨯ P.scheme).hom inferInstance
        (((Scheme.Modules.pullback
          (prod.fst : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
            (Scheme.Modules.dual
              (Scheme.ProjectiveBundle.tautologicalKernel p.left hp))) ⊗
          (Scheme.Modules.pullback
            (prod.snd : P.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
              (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp))
        hTensor q := sorry

/-- The integral class of the identity graph of a represented projective bundle equals
the tautological top Chern class capped with the pullback of the base diagonal. -/
theorem diagonal_formula (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (q : ℕ)
    [IsFiniteLocallyFreeOfRank (q + 1) E] :
    Correspondence.integralGraph (𝟙 P.scheme) =
      Correspondence.castHom (Category.id_comp prod.snd) 0
        (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0) (add_neg_cancel (q : ℤ))
          (BivariantClass.comp (fun _ ↦ 0) (𝟙 (P.scheme ⨯ P.scheme)) prod.snd
            (diagonalChernClass X P E p hp q)
            (baseDiagonalClass X P E p hp q))) := sorry

end AlgebraicGeometry.ChowGroup.ProjectiveBundle
