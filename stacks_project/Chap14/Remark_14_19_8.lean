module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Successor.SimplicialSet
import StacksCheckRecall

/-!
@stack 0189

# Source-facing recall for Remark 14.19.8

The explicit matching-tuple type, its face and degeneracy maps, and its comparison with the
canonical one-step right Kan extension are owned by ReasLib.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.SimplicialObject.Truncated
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject.Truncated

variable {n : ℕ} (U : SSet.Truncated.{u} n)
variable (V : SSet.Truncated.{u} (n + 1))
variable (i : Fin (n + 2)) (j : Fin (n + 1))
variable (x : U.obj (Opposite.op (⦋n⦌ₙ : SimplexCategory.Truncated n)))

/- Remark 14.19.8 (0189) (1): the new top degree is the type of compatible `(n + 2)`-tuples of
`n`-simplices. -/
@[stacks 0189 "Remark 14.19.8 (1)"]
#check (matching.FaceFamily.Tuple U : Type u)

/- Remark 14.19.8 (0189) (2): the top degree of the canonical one-step coskeleton is canonically
isomorphic to the explicit matching-tuple type. -/
@[stacks 0189 "Remark 14.19.8 (2)"]
#check (trunc.cosk.succ.top.tupleIso U :
  ((trunc.cosk.succ n).obj U).obj (successor.top n) ≅ matching.FaceFamily.Tuple U)

/- Remark 14.19.8 (0189) (3): the `i`-th face is the corresponding tuple projection. -/
@[stacks 0189 "Remark 14.19.8 (3)"]
#check (trunc.cosk.succ.top.tupleIso.face_hom U i :
  (trunc.cosk.succ.top.tupleIso U).hom ≫
      matching.FaceFamily.Tuple.π U i =
    ((trunc.cosk.succ n).obj U).δ i ≫
      (trunc.cosk.succ.extension n U).truncIso.hom.app
        (Opposite.op (⦋n⦌ₙ : SimplexCategory.Truncated n)))

/- The inverse tuple classifier recovers each face map. -/
#check (trunc.cosk.succ.top.tupleIso.face_inv U i :
  (trunc.cosk.succ.top.tupleIso U).inv ≫
      ((trunc.cosk.succ n).obj U).δ i ≫
      (trunc.cosk.succ.extension n U).truncIso.hom.app
        (Opposite.op (⦋n⦌ₙ : SimplexCategory.Truncated n)) =
    matching.FaceFamily.Tuple.π U i)

/- Remark 14.19.8 (0189) (4): the `j`-th degeneracy is a function from `n`-simplices to
compatible face tuples. -/
@[stacks 0189 "Remark 14.19.8 (4)"]
#check (trunc.cosk.succ.top.tupleIso.degeneracy_hom U j :
  (trunc.cosk.succ.extension n U).truncIso.inv.app
        (Opposite.op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ≫
      ((trunc.cosk.succ n).obj U).σ j ≫
      (trunc.cosk.succ.top.tupleIso U).hom =
    matching.FaceFamily.Tuple.σ U j)

/- The same degeneracy formula is available in the inverse direction. -/
#check (trunc.cosk.succ.top.tupleIso.degeneracy_inv U j :
  matching.FaceFamily.Tuple.σ U j ≫
      (trunc.cosk.succ.top.tupleIso U).inv =
    (trunc.cosk.succ.extension n U).truncIso.inv.app
        (Opposite.op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ≫
      ((trunc.cosk.succ n).obj U).σ j)

/- Remark 14.19.8 (0189) (5): its `i`-th coordinate is induced by the simplicial composite
`δ_i ≫ σ_j`. -/
@[stacks 0189 "Remark 14.19.8 (5)"]
#check (matching.FaceFamily.Tuple.σ.face U i j x :
  matching.FaceFamily.Tuple.π U i
      (matching.FaceFamily.Tuple.σ U j x) =
    U.map
      (SimplexCategory.Truncated.Hom.tr
        (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op x)

/- Remark 14.19.8 (0189) (6): restriction and canonical one-step extension are inverse through
the universal Hom equivalence. -/
@[stacks 0189 "Remark 14.19.8 (6)"]
#check (trunc.cosk.succ.homEquiv (C := Type u) n U V :
  ((Truncated.trunc (Type u) (n + 1) n (Nat.le_succ n)).obj V ⟶ U) ≃
    (V ⟶ (trunc.cosk.succ n).obj U))

/- Remark 14.19.8 (0189) (7): maps into the tuple type represent compatible face families,
which is the construction applied to `Mor(T, U)` in an arbitrary category. -/
@[stacks 0189 "Remark 14.19.8 (7)"]
#check (matching.FaceFamily.Tuple.representableBy U :
  (matching.FaceFamily.presheaf U).RepresentableBy
    (matching.FaceFamily.Tuple U))

/- The canonical matching object has the same explicit tuple presentation. -/
#check (matching.object.tupleIso U)

/- The generic canonical one-step coskeleton is itself a reusable matching extension. -/
#check (trunc.cosk.succ.extension (C := Type u) n U)

/- Matching objects and explicit tuples vary naturally with the truncated simplicial set. -/
#check (matching.FaceFamily.Tuple.functor n)
#check (matching.FaceFamily.Tuple.functor.yonedaIso.app U)
#check ((matching.functor.yonedaIso (C := Type u) (n := n)).app U)
#check (matching.functor.tupleIso n)
#check (matching.functor.tupleIso.hom_π i)
#check (trunc.cosk.succ.top.tupleIso.natIso n :
  trunc.cosk.succ n ⋙
      (evaluation ((SimplexCategory.Truncated (n + 1))ᵒᵖ) (Type u)).obj
        (successor.top n) ≅
    matching.FaceFamily.Tuple.functor n)

end CategoryTheory.SimplicialObject.Truncated
