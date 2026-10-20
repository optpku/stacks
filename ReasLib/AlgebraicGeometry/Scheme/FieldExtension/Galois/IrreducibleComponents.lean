module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import ReasLib.Topology.IrreducibleComponents.Equiv

/-!
# Galois actions on irreducible components after field extension

The canonical actions use the inverse on `Gal(K / k)` and the direct element
on its opposite. This records the contravariant nature of `Spec` once, while
the lower topological leaf owns the component correspondence of a
homeomorphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Irreducible

/-- The equivalence on irreducible components induced by a Galois automorphism of a
field-extension base change. -/
noncomputable def equiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    irreducibleComponents (FieldExtension.baseChange k K f) ≃
      irreducibleComponents (FieldExtension.baseChange k K f) :=
  (Scheme.homeoOfIso (FieldExtension.Galois.aut k K f σ)).irreducibleComponentsEquiv

/-- The direct-Galois component equivalence is computed by the image of the induced scheme
automorphism. -/
theorem coe_equiv_apply
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k))
    (Z : irreducibleComponents (FieldExtension.baseChange k K f)) :
    ((equiv k K f σ Z :
        irreducibleComponents (FieldExtension.baseChange k K f)) : Set
          (FieldExtension.baseChange k K f)) =
      (Scheme.homeoOfIso (FieldExtension.Galois.aut k K f σ)) '' (Z : Set _) := sorry

/-- The equivalence on irreducible components indexed directly by an element of the opposite
Galois group. -/
noncomputable abbrev opEquiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : (Gal(K/k))ᵐᵒᵖ) :
    irreducibleComponents (FieldExtension.baseChange k K f) ≃
      irreducibleComponents (FieldExtension.baseChange k K f) :=
  equiv k K f σ.unop

/-- The opposite-Galois component equivalence is computed by the image of the induced scheme
automorphism indexed by the underlying Galois element. -/
theorem coe_opEquiv_apply
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : (Gal(K/k))ᵐᵒᵖ)
    (Z : irreducibleComponents (FieldExtension.baseChange k K f)) :
    ((opEquiv k K f σ Z :
        irreducibleComponents (FieldExtension.baseChange k K f)) : Set
          (FieldExtension.baseChange k K f)) =
      (Scheme.homeoOfIso (FieldExtension.Galois.aut k K f σ.unop)) '' (Z : Set _) := sorry

/-- The canonical left `Gal(K / k)` action on irreducible components of a field-extension
base change. -/
noncomputable instance instMulAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MulAction Gal(K/k) (irreducibleComponents (FieldExtension.baseChange k K f)) where
  smul σ := equiv k K f σ.symm
  one_smul := sorry
  mul_smul := sorry

/-- Computation rule for the canonical `Gal(K / k)` action on irreducible components. -/
theorem smul_def
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : Gal(K/k)) (Z : irreducibleComponents (FieldExtension.baseChange k K f)) :
    σ • Z = equiv k K f σ.symm Z := sorry

/-- The canonical left action of the opposite Galois group on irreducible components, with no
inverse hidden in the input element. -/
noncomputable instance instOppositeMulAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MulAction (Gal(K/k))ᵐᵒᵖ (irreducibleComponents (FieldExtension.baseChange k K f)) where
  smul σ := opEquiv k K f σ
  one_smul := sorry
  mul_smul := sorry

/-- Computation rule for the opposite-Galois action on irreducible components. -/
theorem op_smul_def
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : (Gal(K/k))ᵐᵒᵖ) (Z : irreducibleComponents (FieldExtension.baseChange k K f)) :
    σ • Z = opEquiv k K f σ Z := sorry

/-- Fibers of the field-extension component map are exactly opposite-Galois orbits. -/
@[stacks 04KY]
theorem componentsMap_eq_iff_exists_op
    (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T₁ T₂ : irreducibleComponents (FieldExtension.baseChange k ksep f)) :
    FieldExtension.Irreducible.componentsMap k ksep f T₁ =
        FieldExtension.Irreducible.componentsMap k ksep f T₂ ↔
      ∃ σ : (Gal(ksep/k))ᵐᵒᵖ,
        opEquiv k ksep f σ T₁ = T₂ := sorry

end FieldExtension.Galois.Irreducible

end AlgebraicGeometry
