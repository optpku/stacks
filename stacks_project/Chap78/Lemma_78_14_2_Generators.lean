/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import stacks_project.Chap78.Lemma_78_12_3_QCoh

/-!
# Small generating families of equivariant quasi-coherent modules

If the source and target of a groupoid in algebraic spaces are flat, there is a
small family of objects of the equivariant quasi-coherent category such that every
object is the directed colimit of its submodules isomorphic to a family member.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

/-- The subobjects of an equivariant quasi-coherent module that are isomorphic in
`G.QCoh` to some member of a given family. -/
def isoToFamilySubobjects {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Type u} (family : T → G.QCoh) (A : G.QCoh) :
    Set (Subobject A) :=
  { N | ∃ t, Nonempty ((N : G.QCoh) ≅ family t) }

/-- Membership in `isoToFamilySubobjects` means the subobject is isomorphic in `G.QCoh`
to some family member. -/
theorem mem_isoToFamilySubobjects {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Type u} (family : T → G.QCoh) (A : G.QCoh)
    (N : Subobject A) :
    N ∈ isoToFamilySubobjects G family A ↔ ∃ t, Nonempty ((N : G.QCoh) ≅ family t) :=
  sorry

/-- If the source and target of a groupoid in algebraic spaces are flat, there is a
small family of equivariant quasi-coherent modules such that every object is the
directed colimit of its submodules isomorphic to a family member. -/
theorem exists_set_generators {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left] :
    ∃ (T : Type u) (family : T → G.QCoh), ∀ A : G.QCoh,
      DirectedOn (· ≤ ·) (isoToFamilySubobjects G family A) ∧
        IsLUB (isoToFamilySubobjects G family A) (⊤ : Subobject A) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
