/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Immersion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- An immersion into the quotient stack of a smooth groupoid is presented by restriction
to an invariant locally closed subspace, compatibly with the original quotient morphism. -/
theorem existsInvariantLocallyClosedPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ SmallQuotient.quotientStack G) [Immersion i] :
    ∃ W : LocallyClosedSubspace G.U.left,
      CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left W.ι ∧
        ∃ e : SmallQuotient.quotientStack (restrict G W) ≌ Z,
          Nonempty (restrictQuotientHom G W ≅ e.hom ≫ i) := sorry

/-- A closed immersion into the quotient stack of a smooth groupoid is presented by
restriction to an invariant closed subspace, compatibly with the original quotient morphism. -/
theorem existsInvariantClosedPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ SmallQuotient.quotientStack G) [ClosedImmersion i] :
    ∃ W : ClosedSubspace G.U.left,
      CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left W.ι ∧
        ∃ e : SmallQuotient.quotientStack (restrict G W.toLocallyClosed) ≌ Z,
          Nonempty (restrictQuotientHom G W.toLocallyClosed ≅ e.hom ≫ i) := sorry

/-- An open immersion into the quotient stack of a smooth groupoid is presented by
restriction to an invariant open subspace, compatibly with the original quotient morphism. -/
theorem existsInvariantOpenPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ SmallQuotient.quotientStack G) [OpenImmersion i] :
    ∃ W : OpenSubspace G.U.left,
      CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left W.ι ∧
        ∃ e : SmallQuotient.quotientStack (restrict G W.toLocallyClosed) ≌ Z,
          Nonempty (restrictQuotientHom G W.toLocallyClosed ≅ e.hom ≫ i) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
