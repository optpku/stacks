module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.H.Descent
import StacksCheckRecall

/-!
# Lemma 38.35.3

Finite affine h-covering families, their refinements, and equality of
refinements descend along directed inverse limits of affine schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/- Lemma 38.35.3 (1): a standard h covering of an affine directed limit
descends to a standard h covering at one of the affine stages. -/
@[stacks 0EV2] #check
  (AlgebraicGeometry.Scheme.HCovering.Affine.cover_exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [hD_affine : ∀ i : I, IsAffine (D.obj i)] [hlimit_affine : IsAffine c.pt]
      (family : AffineFamilyOver c.pt)
      [hfamily : Scheme.HCovering (fun j : Fin family.n ↦ Over.mk (family.map j))],
      ∃ i : I, ∃ familyAt : AffineFamilyOver (D.obj i),
        Scheme.HCovering (fun j : Fin familyAt.n ↦ Over.mk (familyAt.map j)) ∧
          Nonempty (AffineFamilyOver.IsBaseChangeOf (c.π.app i) familyAt family))

/- Lemma 38.35.3 (2): a refinement between the limit pullbacks of two
standard h coverings descends after passing to a later stage. -/
@[stacks 0EV2] #check
  (AlgebraicGeometry.Scheme.HCovering.Affine.Refinement.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
      {i : I} (sourceAt targetAt : AffineFamilyOver (D.obj i))
      [hsourceAt : Scheme.HCovering
        (fun j : Fin sourceAt.n ↦ Over.mk (sourceAt.map j))]
      [htargetAt : Scheme.HCovering
        (fun j : Fin targetAt.n ↦ Over.mk (targetAt.map j))]
      (limitRefinement : AffineFamilyOver.Refinement
        (sourceAt.pullback (T' := c.pt) (c.π.app i))
        (targetAt.pullback (T' := c.pt) (c.π.app i))),
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

/- Lemma 38.35.3 (3): equality of refinements after pullback to the limit is
detected after pullback to some later affine stage. -/
@[stacks 0EV2] #check
  (AlgebraicGeometry.Scheme.HCovering.Affine.Refinement.eventually_equal :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
      {i : I} (sourceAt targetAt : AffineFamilyOver (D.obj i))
      [hsourceAt : Scheme.HCovering
        (fun j : Fin sourceAt.n ↦ Over.mk (sourceAt.map j))]
      [htargetAt : Scheme.HCovering
        (fun j : Fin targetAt.n ↦ Over.mk (targetAt.map j))]
      (firstAt secondAt : AffineFamilyOver.Refinement sourceAt targetAt),
      firstAt.pullback (T' := c.pt) (c.π.app i) =
        secondAt.pullback (T' := c.pt) (c.π.app i) →
        ∃ i' : I, ∃ hi : i ≤ i',
          firstAt.pullback (T' := D.obj i') (D.map (homOfLE hi)) =
            secondAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
