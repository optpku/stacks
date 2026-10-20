/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

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

/-- A subobject belongs to the family-isomorphic collection exactly when it is
isomorphic in the equivariant category to a family member. -/
theorem mem_isoToFamilySubobjects {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Type u} (family : T → G.QCoh) (A : G.QCoh)
    (N : Subobject A) :
    N ∈ isoToFamilySubobjects G family A ↔ ∃ t, Nonempty ((N : G.QCoh) ≅ family t) :=
  Iff.rfl

/-- The diagram of subobjects isomorphic to family members, with their canonical
inclusion morphisms in the equivariant quasi-coherent category. -/
noncomputable def isoToFamilyDiagram {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Type u} (family : T → G.QCoh) (A : G.QCoh) :
    isoToFamilySubobjects G family A ⥤ G.QCoh :=
  (show Monotone (fun N : isoToFamilySubobjects G family A => N.val) from
    fun _ _ h => h).functor ⋙ Subobject.underlying

/-- The canonical inclusions of the family-isomorphic subobjects form a cocone
with point the ambient equivariant quasi-coherent module. -/
noncomputable def isoToFamilyCocone {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Type u} (family : T → G.QCoh) (A : G.QCoh) :
    Limits.Cocone (isoToFamilyDiagram G family A) where
  pt := A
  ι :=
    { app := fun N => N.val.arrow
      naturality := by
        intro N M f
        change Subobject.underlying.map (homOfLE (leOfHom f) : N.val ⟶ M.val) ≫
          M.val.arrow = N.val.arrow ≫ 𝟙 A
        simpa only [Category.comp_id] using
          (Subobject.underlying_arrow (homOfLE (leOfHom f) : N.val ⟶ M.val)) }

/-- If the source and target of a groupoid in algebraic spaces are flat, there is a
small family of equivariant quasi-coherent modules such that every object is the
directed colimit of its submodules isomorphic to a family member. -/
theorem exists_set_generators {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left] :
    ∃ (T : Type u) (family : T → G.QCoh), ∀ A : G.QCoh,
      (isoToFamilySubobjects G family A).Nonempty ∧
        DirectedOn (· ≤ ·) (isoToFamilySubobjects G family A) ∧
          Nonempty (Limits.IsColimit (isoToFamilyCocone G family A)) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
