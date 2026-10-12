/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced
public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus

/-!
# Geometric reducedness of fibres of morphisms of algebraic spaces

At a point of `Points Y`, geometric reducedness of the scheme-theoretic fibre of a
morphism of algebraic spaces is independent of the field-valued representative, and
equivalent to reducedness of every such fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.29.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `y` be a point of `Points Y`. The following are equivalent:
for some morphism `Spec (.of k) ⟶ Y` in the equivalence class of `y` the algebraic
space `fiberOverField f p` is geometrically reduced over `k`; for every such
morphism the fibre is geometrically reduced over `k`; and for every such morphism
the fibre is reduced. -/
@[stacks 0E07]
theorem geometricallyReducedFiber_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    List.TFAE
      [∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → IsReduced (fiberOverField f p)] :=
  sorry

/-- Existence of a geometrically reduced fibre over some field-valued representative of
`y` is equivalent to geometric reducedness of the fibre over every such representative. -/
theorem exists_geometricallyReduced_fiber_iff_forall
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    (∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p)) ↔
      ∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p) :=
  sorry

/-- Geometric reducedness of the fibre of `f` over every field-valued representative of
`y` is equivalent to reducedness of the fibre over every such representative. -/
theorem forall_geometricallyReduced_fiber_iff_forall_isReduced
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    (∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p)) ↔
      ∀ p : FieldValuedPoint Y, Points.mk p = y → IsReduced (fiberOverField f p) :=
  sorry

/-- Existence of a geometrically reduced fibre over some field-valued representative of
`y` is equivalent to membership of `y` in `geometricallyReducedFiberLocus f`. -/
theorem exists_geometricallyReduced_fiber_iff_mem_locus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    (∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p)) ↔
      y ∈ geometricallyReducedFiberLocus f :=
  sorry

/-- Existence of a geometrically reduced fibre over some field-valued representative of
`y` is equivalent to existence of a morphism `Spec (.of k) ⟶ Y` over `S` representing
`y` whose fibre is geometrically reduced over `k`. -/
theorem exists_geometricallyReduced_fiber_iff_specField
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    (∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p)) ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y),
        Points.mk (FieldValuedPoint.of k σ g) = y ∧
          GeometricallyReduced (fiberOverField f (FieldValuedPoint.of k σ g)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
