module

public import stacks_project.Chap70.Lemma_70_5_7_CompactOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.7: in Situation `70.5.5`, every quasi-compact open subspace `U ⊂ X`
of the directed affine inverse limit is the inverse image of a quasi-compact
open subspace `U_i ⊂ X_i` for some stage `i`. -/
@[stacks 0827] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_quasiCompactOpen_preimage_eq :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (h : j ≤ j'), Affine (D.map (homOfLE h))]
      (U : OpenSubspace c.pt) [IsQuasiCompact U.X],
      ∃ i : I, ∃ Ui : OpenSubspace (D.obj i),
        IsQuasiCompact Ui.X ∧
          Points.map (c.π.app i) ⁻¹' Ui.pointsSet = U.pointsSet)
