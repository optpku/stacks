/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.DirectedLimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AffineFamilyOver

universe u

/- Lemma 61.10.1: for an affine scheme Y and a directed inverse limit of affine
schemes over Y, the singleton family {X → Y} is a standard V covering if and
only if every stage family {X_i → Y} is a standard V covering. -/
@[stacks 0EVN] #check
  (AlgebraicGeometry.AffineFamilyOver.isStandardVCover_limitHom_iff :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {Y : Scheme.{u}} [IsAffine Y]
      (D : OrderDual I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
      (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
      (c : Cone D) (hc : IsLimit c)
      (σlim : c.pt ⟶ Y),
        c.π ≫ t = (Functor.const _).map σlim →
          (IsStandardVCover (singleton σlim (Scheme.isAffine_of_isLimit c hc)) ↔
            ∀ i, IsStandardVCover (singleton (t.app i) inferInstance)))
