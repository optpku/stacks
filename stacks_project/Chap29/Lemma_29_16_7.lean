/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point.Topology

namespace AlgebraicGeometry

universe u

/- Lemma 29.16.7 (1): every nonempty locally closed subset of a scheme meets the set of
finite type points. -/
@[stacks 02J4] #check (AlgebraicGeometry.nonempty_inter_finiteTypePoints :
    ∀ (S : Scheme.{u}) {T : Set S}, T.Nonempty → IsLocallyClosed T →
      (T ∩ finiteTypePoints S).Nonempty)

/- Lemma 29.16.7 (2): for a closed subset `T` of a scheme `S`, the points of finite type in
`S` are dense in `T`, with `T` carrying its subtype topology. -/
@[stacks 02J4] #check (AlgebraicGeometry.dense_finiteTypePoints_in_closed_subset :
  ∀ (S : Scheme.{u}) {T : Set S}, IsClosed T →
    Dense {x : T | (x : S) ∈ finiteTypePoints S})

end AlgebraicGeometry
