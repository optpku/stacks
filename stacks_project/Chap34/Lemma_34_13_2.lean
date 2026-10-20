/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Descent
import StacksCheckRecall

/-!
# Lemma 34.13.2

Standard finite-affine covers, their refinements, and equality of refinements
descend along directed inverse limits of affine schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/- Lemma 34.13.2 (1): a standard cover of an affine directed limit descends
to a standard cover at one of the affine stages. -/
@[stacks 049N] #check
  (AlgebraicGeometry.StandardTopology.Affine.cover_exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c)
      (_ : ∀ i : I, IsAffine (D.obj i)) (τ : StandardTopology)
      (family : AffineFamilyOver c.pt), τ.IsCover family →
        ∃ i : I, ∃ familyAt : AffineFamilyOver (D.obj i),
          τ.IsCover familyAt ∧
            Nonempty (AffineFamilyOver.IsBaseChangeOf
              (c.π.app i) familyAt family))

/- Lemma 34.13.2 (2): a refinement between the canonical limit pullbacks of
two standard covers descends to their canonical pullbacks at a later stage. -/
@[stacks 049N] #check
  (AlgebraicGeometry.StandardTopology.Affine.Refinement.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c)
      [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
      (τ : StandardTopology) {i : I}
      (sourceAt targetAt : AffineFamilyOver (D.obj i)),
      τ.IsCover sourceAt → τ.IsCover targetAt →
      (limitRefinement : AffineFamilyOver.Refinement
        (sourceAt.pullback (T' := c.pt) (c.π.app i))
        (targetAt.pullback (T' := c.pt) (c.π.app i))) →
      ∃ i' : I, ∃ hi : i ≤ i',
        ∃ hsourceLimit :
          AffineFamilyOver.IsBaseChangeOf (c.π.app i')
            (sourceAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
            (sourceAt.pullback (T' := c.pt) (c.π.app i)),
        ∃ htargetLimit :
          AffineFamilyOver.IsBaseChangeOf (c.π.app i')
            (targetAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
            (targetAt.pullback (T' := c.pt) (c.π.app i)),
        ∃ refinement : AffineFamilyOver.Refinement
            (sourceAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
            (targetAt.pullback (T' := D.obj i') (D.map (homOfLE hi))),
          Nonempty (AffineFamilyOver.Refinement.IsBaseChangeOf
            hsourceLimit htargetLimit refinement limitRefinement))

/- Lemma 34.13.2 (3): equality of two refinements after pullback to the limit
is detected after pullback to some later affine stage. -/
@[stacks 049N] #check
  (AlgebraicGeometry.StandardTopology.Affine.Refinement.eventually_equal :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c)
      [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
      (τ : StandardTopology) {i : I}
      (sourceAt targetAt : AffineFamilyOver (D.obj i)),
      τ.IsCover sourceAt → τ.IsCover targetAt →
      (firstAt secondAt : AffineFamilyOver.Refinement sourceAt targetAt) →
      firstAt.pullback (T' := c.pt) (c.π.app i) =
        secondAt.pullback (T' := c.pt) (c.π.app i) →
        ∃ i' : I, ∃ hi : i ≤ i',
          firstAt.pullback (T' := D.obj i') (D.map (homOfLE hi)) =
            secondAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
