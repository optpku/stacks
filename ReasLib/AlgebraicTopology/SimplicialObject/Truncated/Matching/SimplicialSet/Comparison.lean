/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Representability
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.SimplicialSet.Representability
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Matching objects as matching tuples

For truncated simplicial sets, the canonical matching object is canonically isomorphic to the
explicit matching-tuple type. This file owns both the pointwise comparison and its natural
bundling over truncated simplicial sets.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily.Tuple

namespace representableBy

/-- The universal face selected by the tuple representation is the corresponding tuple
projection. -/
@[simp, stacks 0189 "tuple representation on universal faces"]
theorem π {n : ℕ} (U : SSet.Truncated.{u} n) (i : Fin (n + 2)) :
    matching.FaceFamily.π (Tuple.representableBy U) i = Tuple.π U i := sorry

/-- The universal degeneracy selected by the tuple representation is the explicit tuple
degeneracy. -/
@[simp, stacks 0189 "tuple representation on universal degeneracies"]
theorem σ {n : ℕ} (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    matching.FaceFamily.σ (Tuple.representableBy U) j = Tuple.σ U j := sorry

end representableBy

end CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily.Tuple

namespace CategoryTheory.SimplicialObject.Truncated.matching.object

/-- The canonical matching object of a truncated simplicial set is isomorphic to its explicit
type of compatible face tuples. -/
@[stacks 0189 "matching object as compatible tuples"]
noncomputable def tupleIso {n : ℕ} (U : SSet.Truncated.{u} n) :
    matching.object U ≅ matching.FaceFamily.Tuple U :=
  Functor.RepresentableBy.uniqueUpToIso
    (matching.object.representableBy U)
    (matching.FaceFamily.Tuple.representableBy U)

namespace tupleIso

/-- The forward matching-object/tuple comparison identifies every face projection. -/
@[reassoc (attr := simp), stacks 0189 "matching-object tuple comparison on faces"]
theorem hom_π {n : ℕ} (U : SSet.Truncated.{u} n) (i : Fin (n + 2)) :
    (tupleIso U).hom ≫ matching.FaceFamily.Tuple.π U i =
      matching.object.face U i := sorry

/-- The canonical matching-object degeneracy becomes the explicit tuple degeneracy under the
matching-object/tuple comparison. -/
@[reassoc (attr := simp), stacks 0189 "matching-object tuple comparison on degeneracies"]
theorem σ_hom {n : ℕ} (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    matching.object.σ U j ≫ (tupleIso U).hom =
      matching.FaceFamily.Tuple.σ U j := sorry

/-- The inverse matching-object/tuple comparison identifies every face projection. -/
@[reassoc (attr := simp), stacks 0189 "inverse matching-object tuple comparison on faces"]
theorem inv_face {n : ℕ} (U : SSet.Truncated.{u} n) (i : Fin (n + 2)) :
    (tupleIso U).inv ≫ matching.object.face U i =
      matching.FaceFamily.Tuple.π U i := sorry

/-- The inverse matching-object/tuple comparison carries an explicit tuple degeneracy to the
canonical matching-object degeneracy. -/
@[reassoc (attr := simp), stacks 0189 "inverse matching-object tuple comparison on degeneracies"]
theorem σ_inv {n : ℕ} (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    matching.FaceFamily.Tuple.σ U j ≫ (tupleIso U).inv =
      matching.object.σ U j := sorry

/-- The pointwise matching-object/tuple comparisons are natural in the truncated simplicial
set. -/
@[stacks 0189 "naturality of the matching-object tuple comparison"]
theorem hom_naturality {n : ℕ} {U V : SSet.Truncated.{u} n} (α : U ⟶ V) :
    matching.map α ≫ (tupleIso V).hom =
      (tupleIso U).hom ≫ matching.FaceFamily.Tuple.map α := sorry

end tupleIso

end CategoryTheory.SimplicialObject.Truncated.matching.object

namespace CategoryTheory.SimplicialObject.Truncated.matching.functor

/-- The canonical matching-object functor on truncated simplicial sets is naturally isomorphic
to the explicit matching-tuple functor. -/
@[stacks 0189 "matching-object functor as compatible tuples"]
noncomputable def tupleIso (n : ℕ) :
    matching.functor (C := Type u) n ≅ matching.FaceFamily.Tuple.functor n :=
  NatIso.ofComponents (fun U ↦ matching.object.tupleIso U)
    (fun {U V} α ↦ matching.object.tupleIso.hom_naturality (U := U) (V := V) α)

namespace tupleIso

/-- The component of the functorial matching-object/tuple comparison is the canonical pointwise
comparison. -/
@[simp, stacks 0189 "component of the matching-object tuple comparison"]
theorem app {n : ℕ} (U : SSet.Truncated.{u} n) :
    (matching.functor.tupleIso n).app U = matching.object.tupleIso U := sorry

/-- The natural matching-object/tuple comparison carries canonical faces to tuple
projections. -/
@[reassoc (attr := simp), stacks 0189 "natural matching-object tuple comparison on faces"]
theorem hom_π {n : ℕ} (i : Fin (n + 2)) :
    (matching.functor.tupleIso n).hom ≫
        matching.FaceFamily.Tuple.functor.π i =
      matching.functor.face (C := Type u) i := sorry

/-- The inverse natural matching-object/tuple comparison carries tuple projections to
canonical faces. -/
@[reassoc (attr := simp), stacks 0189 "inverse natural matching-object tuple comparison on faces"]
theorem inv_face {n : ℕ} (i : Fin (n + 2)) :
    (matching.functor.tupleIso n).inv ≫
        matching.functor.face (C := Type u) i =
      matching.FaceFamily.Tuple.functor.π i := sorry

/-- The forward functorial comparison carries the canonical matching-object degeneracy at each
truncated simplicial set to the natural tuple degeneracy. -/
@[reassoc (attr := simp), stacks 0189 "functorial matching-object tuple comparison on degeneracies"]
theorem σ_hom_app {n : ℕ} (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    matching.object.σ U j ≫ (matching.functor.tupleIso n).hom.app U =
      (matching.FaceFamily.Tuple.functor.σ j).app U := sorry

/-- The inverse functorial comparison carries the natural tuple degeneracy at each truncated
simplicial set to the canonical matching-object degeneracy. -/
@[reassoc (attr := simp), stacks 0189 "inverse functorial matching-object tuple comparison on degeneracies"]
theorem σ_inv_app {n : ℕ} (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    (matching.FaceFamily.Tuple.functor.σ j).app U ≫
        (matching.functor.tupleIso n).inv.app U =
      matching.object.σ U j := sorry

end tupleIso

end CategoryTheory.SimplicialObject.Truncated.matching.functor
