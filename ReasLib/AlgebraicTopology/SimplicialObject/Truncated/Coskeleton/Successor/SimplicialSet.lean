module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Successor
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.SimplicialSet.Comparison
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0189

# Successor coskeletons of truncated simplicial sets

The top degree of the canonical one-step coskeleton of a truncated simplicial set is identified
with its explicit matching-tuple type. The comparison exposes both directions of the face and
degeneracy formulas.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject.Truncated.trunc.cosk.succ.top

/-- The top degree of the canonical one-step coskeleton of a truncated simplicial set is the
explicit type of compatible face tuples. -/
@[stacks 0189 "one-step coskeleton top degree as compatible tuples"]
noncomputable def tupleIso {n : ℕ} (U : SSet.Truncated.{u} n) :
    ((trunc.cosk.succ n).obj U).obj (successor.top n) ≅
      matching.FaceFamily.Tuple U :=
  trunc.cosk.succ.top.iso n U ≪≫ (matching.functor.tupleIso n).app U

namespace tupleIso

/-- Under the explicit tuple presentation, an actual top face of the one-step coskeleton is the
corresponding tuple projection, after identifying the retained degree with `U`. -/
@[reassoc (attr := simp), stacks 0189 "one-step coskeleton face as a tuple projection"]
theorem face_hom {n : ℕ} (U : SSet.Truncated.{u} n) (i : Fin (n + 2)) :
    (tupleIso U).hom ≫ matching.FaceFamily.Tuple.π U i =
      ((trunc.cosk.succ n).obj U).δ i ≫
        (trunc.cosk.succ.extension n U).truncIso.hom.app
          (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) := sorry

/-- The inverse tuple presentation carries each tuple projection to the corresponding actual top
face, followed by the identification of the retained degree with `U`. -/
@[reassoc (attr := simp), stacks 0189 "inverse one-step coskeleton tuple comparison on faces"]
theorem face_inv {n : ℕ} (U : SSet.Truncated.{u} n) (i : Fin (n + 2)) :
    (tupleIso U).inv ≫ ((trunc.cosk.succ n).obj U).δ i ≫
        (trunc.cosk.succ.extension n U).truncIso.hom.app
          (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) =
      matching.FaceFamily.Tuple.π U i := sorry

/-- Under the explicit tuple presentation, an actual top degeneracy of the one-step coskeleton
is the tuple whose coordinates are the composites `δ_i ≫ σ_j`. -/
@[reassoc (attr := simp), stacks 0189 "one-step coskeleton degeneracy as a matching tuple"]
theorem degeneracy_hom {n : ℕ} (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    (trunc.cosk.succ.extension n U).truncIso.inv.app
          (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ≫
        ((trunc.cosk.succ n).obj U).σ j ≫ (tupleIso U).hom =
      matching.FaceFamily.Tuple.σ U j := sorry

/-- The inverse tuple presentation sends an explicit tuple degeneracy to the actual top
degeneracy after identifying `U` with the retained degree. -/
@[reassoc (attr := simp), stacks 0189 "inverse one-step coskeleton tuple comparison on degeneracies"]
theorem degeneracy_inv {n : ℕ} (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    matching.FaceFamily.Tuple.σ U j ≫ (tupleIso U).inv =
      (trunc.cosk.succ.extension n U).truncIso.inv.app
          (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ≫
        ((trunc.cosk.succ n).obj U).σ j := sorry

/-- The top-degree tuple comparisons are natural in the truncated simplicial set. -/
@[stacks 0189 "naturality of the one-step coskeleton tuple comparison"]
theorem naturality {n : ℕ} {U V : SSet.Truncated.{u} n} (f : U ⟶ V) :
    ((trunc.cosk.succ n).map f).app (successor.top n) ≫ (tupleIso V).hom =
      (tupleIso U).hom ≫ matching.FaceFamily.Tuple.map f := sorry

/-- The top degree of the one-step coskeleton is naturally the matching-tuple functor. -/
@[stacks 0189 "natural one-step coskeleton tuple comparison"]
noncomputable def natIso (n : ℕ) :
    trunc.cosk.succ n ⋙
        (evaluation ((SimplexCategory.Truncated (n + 1))ᵒᵖ) (Type u)).obj
          (successor.top n) ≅
      matching.FaceFamily.Tuple.functor n :=
  NatIso.ofComponents (fun U ↦ tupleIso U)
    (fun f ↦ tupleIso.naturality f)

namespace natIso

/-- A component of the natural top-degree tuple comparison is the canonical objectwise tuple
comparison. -/
@[simp, stacks 0189 "component of the natural one-step tuple comparison"]
theorem app (n : ℕ) (U : SSet.Truncated.{u} n) :
    (natIso n).app U = tupleIso U := sorry

end natIso

end tupleIso

end CategoryTheory.SimplicialObject.Truncated.trunc.cosk.succ.top
