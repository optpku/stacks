module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced.StructureSheaf

/-!
# Reduced algebraic spaces

An algebraic space is reduced if and only if every local ring is reduced. In that case the
ring of global sections is reduced, and a global function vanishing everywhere is zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.21.4

An algebraic space is reduced if and only if all of its local rings are reduced.
-/
@[stacks 0BGS] #check
  (AlgebraicGeometry.AlgebraicSpace.isReduced_iff_localRingHas :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      AlgebraicGeometry.AlgebraicSpace.IsReduced X ↔
        ∀ x : Points X, localRingHas (fun R ↦ _root_.IsReduced R) X x)

#check
  (AlgebraicGeometry.AlgebraicSpace.isReduced_globalSectionsRing :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [AlgebraicGeometry.AlgebraicSpace.IsReduced X],
      _root_.IsReduced (globalSectionsRing X))

#check
  (AlgebraicGeometry.AlgebraicSpace.eq_zero_of_zeroLocus_eq_univ :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [AlgebraicGeometry.AlgebraicSpace.IsReduced X]
      (f : globalSectionsRing X), X.zeroLocus {f} = Set.univ → f = 0)

end AlgebraicGeometry.AlgebraicSpace
