/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.BoundaryCylinder
import StacksCheckRecall

/-!
# Internal hom and the homotopy-extension pushout

The reusable statement is owned by the boundary-cylinder specialization leaf
`ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.BoundaryCylinder`.
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (n : ℕ) (L : SimplicialObject C)

/- Lemma 25.9.1 [stacks 01GP]: the smallest simplicial subset `U` containing the two
endpoints and the boundary cylinder is canonically modeled by the `Subcomplex.unionProd`
pushout. After the standard degree and coskeleton identifications, its mapping object is the
pullback of the two restriction maps. This is the boundary-cylinder specialization of the
general internal-hom pushout theorem, with `k = n + 1`. -/
@[stacks 01GP] #check
  @CategoryTheory.SimplicialObject.internalHom.boundaryCylinder.isPullback C _ (n + 1) L
