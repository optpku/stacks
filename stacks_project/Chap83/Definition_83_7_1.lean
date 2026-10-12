/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Topological
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.PreRelation

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariantHom φ)
variable (Q : ∀ {U' X' : Over B} (P' : PreRelation U') (φ' : U' ⟶ X'),
  P'.IsInvariantHom φ' → Prop)

/- Definition 83.7.1 (1): the morphism `φ` is submersive. -/
@[stacks 04A4] #check (AlgebraicGeometry.AlgebraicSpace.Submersive φ.left : Prop)

/- Definition 83.7.1 (2): for any `R`-invariant closed subset `Z` of `Points U.left`, the
image `Points.map φ.left '' Z` is closed in `Points X.left`. -/
@[stacks 04A4] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.MapsInvariantClosed P φ : Prop)

/- Definition 83.7.1 (3): condition (2) holds and `φ` preserves binary intersections of
`R`-invariant closed subsets of `Points U.left`. -/
@[stacks 04A4] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IntersectInvariantClosed P φ : Prop)

/- Definition 83.7.1 (4): the morphism `(t, s) : R ⟶ U ×_X U` is universally submersive. -/
@[stacks 04A4] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.inducedUniversallySubmersive P hφ : Prop)

/- Definition 83.7.1 (5): a listed condition holds uniformly when it holds after any flat
base change, in the sense of Definition 83.3.4. -/
@[stacks 04A4] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.holdsUniformly P hφ Q : Prop)

/- Definition 83.7.1 (6): a listed condition holds universally when it holds after any base
change, in the sense of Definition 83.3.4. -/
@[stacks 04A4] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.holdsUniversally P hφ Q : Prop)
