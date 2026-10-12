/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.ClosedSubscheme
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.52.9: an open subscheme disjoint from the fibre through a point but
whose closure contains that point yields the closed subscheme of Lemma 37.52.7. -/
@[stacks 05GW] #check
  (AlgebraicGeometry.Scheme.Hom.exists_closedSubscheme_quasiFiniteAt_of_mem_closure :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      [IsLocallyNoetherian S] (x : X) (U : X.Opens),
      f.asFiber x ∈ closedPoints (f.fiber (f x)) →
      Disjoint (U : Set X) (f ⁻¹' {f x}) →
      x ∈ closure (U : Set X) →
      ∃ (Z : X.IdealSheafData) (hxZ : x ∈ Z.support),
        FiniteType.QuasiFiniteAt (Z.subschemeι ≫ f) ⟨x, hxZ⟩ ∧
          ∃ z : X, z ∈ Z.support ∧ z ∈ U ∧
            Specializes z x ∧ f z ≠ f x)

end AlgebraicGeometry.Scheme.Hom

end
