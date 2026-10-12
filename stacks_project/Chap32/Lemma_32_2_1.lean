/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 32.2.1

The explicit affine directed-limit construction is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

noncomputable section

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i, IsAffine (D.obj i)]

/- Lemma 32.2.1: The explicit affine cone on
`Spec (colimit (D.op ⋙ Scheme.Γ))` is a limit cone. -/
@[stacks 01YW] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.cone_isLimit D :
    IsLimit (AlgebraicGeometry.Scheme.Limit.DirectedAffine.cone D))

#check (AlgebraicGeometry.Scheme.Limit.DirectedAffine.scheme D : Scheme.{u})

#check (AlgebraicGeometry.Scheme.Limit.DirectedAffine.cone D : Cone D)

#check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.cone_π_app D :
    ∀ i : OrderDual I,
      (AlgebraicGeometry.Scheme.Limit.DirectedAffine.cone D).π.app i =
        Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (Opposite.op i)) ≫
          (D.obj i).isoSpec.inv)

#check
  (AlgebraicGeometry.isAffine_Spec (colimit (D.op ⋙ Scheme.Γ)) :
    IsAffine (AlgebraicGeometry.Scheme.Limit.DirectedAffine.scheme D))
