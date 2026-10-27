/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.ImmersedSubstack
import StacksCheckRecall

/-!
# Immersions into presentations

An immersion into the quotient stack of a smooth groupoid in algebraic spaces
cuts out an invariant locally closed subspace of the object space, whose
restricted groupoid presents the source of the immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 100.9.7 (1): An immersion is presented by an invariant locally closed subspace,
with a 2-commutative triangle over the original quotient stack. -/
@[stacks 0505] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.existsInvariantLocallyClosedPresentation :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
      (i : Z ⟶ SmallQuotient.quotientStack G) [Immersion i],
      ∃ W : LocallyClosedSubspace G.U.left,
        CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left W.ι ∧
          ∃ e : SmallQuotient.quotientStack (restrict G W) ≌ Z,
            Nonempty (restrictQuotientHom G W ≅ e.hom ≫ i))

/- Lemma 100.9.7 (2): A closed immersion is presented by an invariant closed subspace,
with a 2-commutative triangle over the original quotient stack. -/
@[stacks 0505] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.existsInvariantClosedPresentation :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
      (i : Z ⟶ SmallQuotient.quotientStack G) [ClosedImmersion i],
      ∃ W : ClosedSubspace G.U.left,
        CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left W.ι ∧
          ∃ e : SmallQuotient.quotientStack (restrict G W.toLocallyClosed) ≌ Z,
            Nonempty (restrictQuotientHom G W.toLocallyClosed ≅ e.hom ≫ i))

/- Lemma 100.9.7 (3): An open immersion is presented by an invariant open subspace,
with a 2-commutative triangle over the original quotient stack. -/
@[stacks 0505] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.existsInvariantOpenPresentation :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
      (i : Z ⟶ SmallQuotient.quotientStack G) [OpenImmersion i],
      ∃ W : OpenSubspace G.U.left,
        CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left W.ι ∧
          ∃ e : SmallQuotient.quotientStack (restrict G W.toLocallyClosed) ≌ Z,
            Nonempty (restrictQuotientHom G W.toLocallyClosed ≅ e.hom ≫ i))

end AlgebraicGeometry.GroupoidAlgebraicSpace
