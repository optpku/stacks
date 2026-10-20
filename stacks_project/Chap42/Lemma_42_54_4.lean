/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.Excess

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ShortExact

/- Lemma 42.54.4: the completed excess-intersection formula for a cartesian square
of closed immersions with a compatible finite locally free short exact sequence. -/
@[stacks 0FV7] #check
  (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ShortExact.closedClassBaseChange_eq_topChern_comp :
    ∀
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
      square V).map = Scheme.Modules.dualMap ι ≫ V'.map),
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
              (globalClassOfRank delta (i' ≫ p') p' i' rfl V' D' ranks.1))))))

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ShortExact
