/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ShortExact

/-- The restriction of an immersion to the joint rank locus of a virtual normal
bundle and a finite locally free module, with the full target retained. -/
def jointRankHom {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X)
    [IsImmersion i] (V' : VirtualNormalBundle i) (E : Z.Modules)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    BivariantClass.ComponentRestriction.over (Over.mk (i ≫ p))
        (@rankOpen Z X i (inferInstance : IsImmersion i) V' r' ⊓ (Scheme.Modules.rankClopen E rE).toOpens) ⟶
      BivariantClass.ComponentRestriction.over (Over.mk p) ⊤ :=
  BivariantClass.ComponentRestriction.hom (overHom (i ≫ p) p i rfl)
    (@rankOpen Z X i (inferInstance : IsImmersion i) V' r' ⊓ (Scheme.Modules.rankClopen E rE).toOpens) ⊤
    (by rw [Scheme.Hom.preimage_top]; exact le_top)

/-- The underlying map on a joint rank locus is the open restriction of the immersion. -/
theorem jointRankHom_left {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X)
    [IsImmersion i] (V' : VirtualNormalBundle i) (E : Z.Modules)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    (jointRankHom p i V' E r' rE).left =
      i.resLE ⊤ (@rankOpen Z X i (inferInstance : IsImmersion i) V' r' ⊓ (Scheme.Modules.rankClopen E rE).toOpens)
        (by rw [Scheme.Hom.preimage_top]; exact le_top) := rfl

/-- The canonical top Chern component of a finite locally free module restricted
further to a joint rank locus with a virtual normal bundle. -/
def jointRankTopChern
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) (i : Z ⟶ X)
    [LocallyOfFiniteType (i ≫ p)] [IsImmersion i]
    (V' : VirtualNormalBundle i) (E : Z.Modules) [E.IsFiniteLocallyFree]
    (r' rE : ℕ) :
    ChowCohomology.degree delta
      (BivariantClass.ComponentRestriction.over (Over.mk (i ≫ p))
        (@rankOpen Z X i (inferInstance : IsImmersion i) V' r' ⊓ (Scheme.Modules.rankClopen E rE).toOpens)).hom (rE : ℤ) :=
  ChowCohomology.restrictDegree delta
    (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk (i ≫ p)))
      (@rankOpen Z X i (inferInstance : IsImmersion i) V' r' ⊓ (Scheme.Modules.rankClopen E rE).toOpens)
      (Scheme.Modules.rankClopen E rE).toOpens (by exact inf_le_right)) (rE : ℤ)
    (ChernClass.rankComponent delta (i ≫ p) E rE ⟨rE, Nat.lt_succ_self rE⟩)

/-- The joint-rank top Chern class is the restriction of the canonical component
on the rank locus of the finite locally free module. -/
theorem jointRankTopChern_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) (i : Z ⟶ X)
    [LocallyOfFiniteType (i ≫ p)] [IsImmersion i]
    (V' : VirtualNormalBundle i) (E : Z.Modules) [E.IsFiniteLocallyFree]
    (r' rE : ℕ) :
    jointRankTopChern delta p i V' E r' rE =
      ChowCohomology.restrictDegree delta
        (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk (i ≫ p)))
          (@rankOpen Z X i (inferInstance : IsImmersion i) V' r' ⊓ (Scheme.Modules.rankClopen E rE).toOpens)
          (Scheme.Modules.rankClopen E rE).toOpens (by exact inf_le_right)) (rE : ℤ)
        (ChernClass.rankComponent delta (i ≫ p) E rE ⟨rE, Nat.lt_succ_self rE⟩) := rfl

/-- For a cartesian square of closed immersions and a compatible finite locally free
short exact sequence from the new virtual normal bundle into the pulled original bundle,
restriction of the original class equals the quotient top Chern class composed with the
new virtual-normal class, as completed families on all joint rank loci. -/
theorem closedClassBaseChange_eq_topChern_comp
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (p' : X' ⟶ S) [LocallyOfFiniteType p']
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [IsClosedImmersion i]
    (i' : Z' ⟶ X') [LocallyOfFiniteType (i' ≫ p')] [IsClosedImmersion i']
    (g : Over.mk (i' ≫ p') ⟶ Over.mk (i ≫ p)) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i) (V' : VirtualNormalBundle i')
    (D : ClosedDeformation (i ≫ p) p i rfl V)
    (D' : ClosedDeformation (i' ≫ p') p' i' rfl V') (E : Z'.Modules)
    (ι : V'.module ⟶ (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
      (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
      square V).module)
    (πE : (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
      (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
      square V).module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree]
    (hshort : (ShortComplex.mk ι πE hzero).ShortExact)
    (hfactor : (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
      (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
      square V).map = Scheme.Modules.dualMap ι ≫ V'.map) :
    ((fun ranks : ℕ × ℕ ↦
      @DirectSum.of ℕ
        (fun n : ℕ ↦ BivariantClass delta
          (jointRankHom p' i' V' E ranks.1 ranks.2) (n : ℤ))
        (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
          (jointRankHom p' i' V' E ranks.1 ranks.2) (n : ℤ)).toAddCommMonoid)
        inferInstance (ranks.1 + ranks.2)
        (BivariantClass.ComponentRestriction.restrict delta
          (overHom (i' ≫ p') p' i' rfl) (ranks.1 + ranks.2 : ℤ)
          (@rankOpen Z' X' i' (inferInstance : IsImmersion i') V' ranks.1 ⊓ (Scheme.Modules.rankClopen E ranks.2).toOpens) ⊤
          (by rw [Scheme.Hom.preimage_top]; exact le_top)
          (BivariantClass.restrict delta (f := overHom (i ≫ p) p i rfl)
            g (overHom (i' ≫ p') p' i' rfl) f
            square (ranks.1 + ranks.2 : ℤ)
            (globalClassOfRank delta (i ≫ p) p i rfl V D (ranks.1 + ranks.2))))) :
      BivariantClass.OpenRestriction.Completion delta (overHom (i' ≫ p') p' i' rfl)
        (fun ranks : ℕ × ℕ ↦
          @rankOpen Z' X' i' (inferInstance : IsImmersion i') V' ranks.1 ⊓ (Scheme.Modules.rankClopen E ranks.2).toOpens)
        (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
        (fun _ ↦ by rw [Scheme.Hom.preimage_top]; exact le_top)) =
    (fun ranks : ℕ × ℕ ↦
      BivariantClass.Nonnegative.castHom delta
        (Category.id_comp (jointRankHom p' i' V' E ranks.1 ranks.2))
        (BivariantClass.Nonnegative.comp delta
          (𝟙 (BivariantClass.ComponentRestriction.over (Over.mk (i' ≫ p'))
            (@rankOpen Z' X' i' (inferInstance : IsImmersion i') V' ranks.1 ⊓ (Scheme.Modules.rankClopen E ranks.2).toOpens)))
          (jointRankHom p' i' V' E ranks.1 ranks.2)
          (@DirectSum.of ℕ
            (fun n : ℕ ↦ BivariantClass delta
              (𝟙 (BivariantClass.ComponentRestriction.over (Over.mk (i' ≫ p'))
                (@rankOpen Z' X' i' (inferInstance : IsImmersion i') V' ranks.1 ⊓ (Scheme.Modules.rankClopen E ranks.2).toOpens)))
              (n : ℤ))
            (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
              (𝟙 (BivariantClass.ComponentRestriction.over (Over.mk (i' ≫ p'))
                (@rankOpen Z' X' i' (inferInstance : IsImmersion i') V' ranks.1 ⊓
                  (Scheme.Modules.rankClopen E ranks.2).toOpens))) (n : ℤ)).toAddCommMonoid)
            inferInstance ranks.2
            (jointRankTopChern delta p' i' V' E ranks.1 ranks.2))
          (@DirectSum.of ℕ
            (fun n : ℕ ↦ BivariantClass delta
              (jointRankHom p' i' V' E ranks.1 ranks.2) (n : ℤ))
            (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
              (jointRankHom p' i' V' E ranks.1 ranks.2) (n : ℤ)).toAddCommMonoid)
            inferInstance ranks.1
            (BivariantClass.ComponentRestriction.restrict delta
              (overHom (i' ≫ p') p' i' rfl) (ranks.1 : ℤ)
              (@rankOpen Z' X' i' (inferInstance : IsImmersion i') V' ranks.1 ⊓ (Scheme.Modules.rankClopen E ranks.2).toOpens) ⊤
              (by rw [Scheme.Hom.preimage_top]; exact le_top)
              (globalClassOfRank delta (i' ≫ p') p' i' rfl V' D' ranks.1))))) := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ShortExact
