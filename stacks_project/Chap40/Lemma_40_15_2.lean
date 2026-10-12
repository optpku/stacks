/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.SubsetSections.BaseChange
import StacksCheckRecall

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 40.15.2: in a cartesian square over a flat map `A ⟶ B`, if `Y` is
quasi-separated and `E` is a nonempty intersection of quasi-compact opens, then the sections
of the restricted structure sheaf on `f ⁻¹' E` are the scalar extension of the sections on
`E`. -/
@[stacks 0APJ] #check
  (AlgebraicGeometry.Scheme.Hom.subsetSections_tensorProduct_of_flat :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {X Y : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of B))
      (q : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
      (sq : IsPullback p f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) q)
      [Module.Flat A B] [QuasiSeparatedSpace Y]
        (E : Set Y)
        (hE : ∃ S : Set (CompactOpens Y), S.Nonempty ∧ E = ⋂ U ∈ S, (U : Set Y)),
        IsIsomorphic
          (AlgebraicGeometry.Scheme.subsetSectionsRing X (f ⁻¹' E))
          (CommRingCat.of
            (TensorProduct A
              (AlgebraicGeometry.Scheme.Hom.subsetSectionsAlg q E) B)))
