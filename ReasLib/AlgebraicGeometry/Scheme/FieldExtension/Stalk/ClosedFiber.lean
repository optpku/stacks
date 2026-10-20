/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Basic
public import ReasLib.RingTheory.RingHom.Fiber.Quotient

/-!
# Closed fibres at field-extension base-change points

This leaf builds the closed-fibre quotient of a base-change stalk and records
its compatible algebra structures.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Pullback
open scoped TensorProduct Algebra.TensorProduct.Right

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Stalk.ClosedFiber

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The extension of the source maximal ideal to a field-extension base-change stalk. -/
abbrev ideal
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Ideal ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  Ideal.map (FieldExtension.Stalk.toSourceMap k K f y).hom
    (IsLocalRing.maximalIdeal
      (X.presheaf.stalk (FieldExtension.toSource k K f y)))

/-- The quotient presentation of the closed fibre at a field-extension base-change point. -/
abbrev quotient
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) : Type u :=
  ((FieldExtension.baseChange k K f).presheaf.stalk y) ⧸
    ideal k K f y

namespace Source

/-- The source-stalk maximal ideal is contained in the pullback of the closed-fibre ideal. -/
theorem maximalIdeal_le_comap
    (y : FieldExtension.baseChange k K f) :
    IsLocalRing.maximalIdeal
        (X.presheaf.stalk (FieldExtension.toSource k K f y)) ≤
      Ideal.comap
        (algebraMap
          (X.presheaf.stalk (FieldExtension.toSource k K f y))
          ((FieldExtension.baseChange k K f).presheaf.stalk y))
        (ideal k K f y) := sorry

/-- The canonical algebra structure from the source residue field to the closed fibre. -/
noncomputable abbrev algebra
    (y : FieldExtension.baseChange k K f) :
    Algebra (X.residueField (FieldExtension.toSource k K f y))
      (quotient k K f y) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (maximalIdeal_le_comap f y)

/-- Typeclass bridge for the source-residue-field algebra on the closed fibre. -/
noncomputable instance instAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra (X.residueField (FieldExtension.toSource k K f y))
      (quotient k K f y) :=
  algebra f y

end Source

namespace Quotient

/-- The closed-fibre quotient, presented as the canonical residue-field fiber of the source-stalk
map. -/
noncomputable abbrev equiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    quotient k K f y ≃ₐ[((FieldExtension.baseChange k K f).presheaf.stalk y)]
      (IsLocalRing.maximalIdeal
        (X.presheaf.stalk (FieldExtension.toSource k K f y))).Fiber
        ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  Ideal.Fiber.maximalQuotientAlgEquiv
    (R := X.presheaf.stalk (FieldExtension.toSource k K f y))
    (S := (FieldExtension.baseChange k K f).presheaf.stalk y)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (FieldExtension.toSource k K f y)))

/-- The closed-fibre-to-fiber equivalence sends a stalk element modulo the extended maximal ideal
to its canonical image in the residue-field fiber. -/
@[simp]
theorem equiv_apply_mk
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f)
    (s : (FieldExtension.baseChange k K f).presheaf.stalk y) :
    equiv k K f y (Ideal.Quotient.mk (ideal k K f y) s) =
      algebraMap ((FieldExtension.baseChange k K f).presheaf.stalk y)
        ((IsLocalRing.maximalIdeal
          (X.presheaf.stalk (FieldExtension.toSource k K f y))).Fiber
          ((FieldExtension.baseChange k K f).presheaf.stalk y)) s := sorry

/-- The inverse closed-fibre-to-fiber equivalence sends the canonical stalk image to its quotient
class. -/
@[simp]
theorem equiv_symm_apply_algebraMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f)
    (s : (FieldExtension.baseChange k K f).presheaf.stalk y) :
    (equiv k K f y).symm
      (algebraMap ((FieldExtension.baseChange k K f).presheaf.stalk y)
        ((IsLocalRing.maximalIdeal
          (X.presheaf.stalk (FieldExtension.toSource k K f y))).Fiber
          ((FieldExtension.baseChange k K f).presheaf.stalk y)) s) =
      Ideal.Quotient.mk (ideal k K f y) s := sorry

end Quotient

namespace Tensor

/-- The canonical morphism from the pullback-point tensor ring to the closed fibre. -/
noncomputable abbrev map
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    FieldExtension.Stalk.pointTensor k K f y ⟶
      CommRingCat.of (quotient k K f y) :=
  pushout.desc
    (CommRingCat.ofHom
        (algebraMap
          (X.residueField (FieldExtension.toSource k K f y))
          (quotient k K f y)))
    (CommRingCat.ofHom
      ((algebraMap K (quotient k K f y)).comp
        (FieldExtension.Stalk.BaseChange.residueMap k K f y)))
    sorry

/-- The closed-fibre map from the point tensor product restricts on the source residue-field leg
to its canonical algebra map. -/
theorem inl_comp_map
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    (Triplet.ofPoint y).tensorInl ≫ map k K f y =
      CommRingCat.ofHom
        (algebraMap
          (X.residueField (FieldExtension.toSource k K f y))
          (quotient k K f y)) := sorry

/-- The closed-fibre map from the point tensor product restricts on the `Spec K` residue-field leg
to the canonical map through `K`. -/
theorem inr_comp_map
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    (Triplet.ofPoint y).tensorInr ≫ map k K f y =
      CommRingCat.ofHom
        ((algebraMap K (quotient k K f y)).comp
          (FieldExtension.Stalk.BaseChange.residueMap k K f y)) := sorry

/-- The canonical algebra structure from the pullback-point tensor ring to the closed fibre. -/
noncomputable abbrev algebra
    (y : FieldExtension.baseChange k K f) :
    Algebra (FieldExtension.Stalk.pointTensor k K f y)
      (quotient k K f y) :=
  (map k K f y).hom.toAlgebra

/-- Typeclass bridge for the pullback-point tensor algebra on the closed fibre. -/
noncomputable instance instAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra (FieldExtension.Stalk.pointTensor k K f y)
      (quotient k K f y) :=
  algebra f y

end Tensor

end FieldExtension.Stalk.ClosedFiber

end AlgebraicGeometry
