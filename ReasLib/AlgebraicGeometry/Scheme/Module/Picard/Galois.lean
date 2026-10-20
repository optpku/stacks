module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.FieldTheory.KrullTopology
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.FieldExtension

/-!
# Galois action on Picard groups after field extension

Pullback along the automorphisms of a field-extension base change gives the canonical left
Galois action on its Picard group.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Picard

/-- The canonical left Galois action on the Picard group after field extension. -/
@[implicit_reducible]
noncomputable def galoisAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    DistribMulAction Gal(K/k) (FieldExtension.baseChange k K f).PicardGroup where
  smul σ x := Scheme.Hom.picardPullback (FieldExtension.Galois.map k K f σ) x
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry

/-- The Galois action on Picard classes is pullback along the induced base-change
automorphism. -/
theorem galoisAction_apply
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : Gal(K/k)) (x : (FieldExtension.baseChange k K f).PicardGroup) :
    (galoisAction k K f).toMulAction.toSMul.smul σ x =
      Scheme.Hom.picardPullback (FieldExtension.Galois.map k K f σ) x := sorry

/-- The subgroup of Picard classes fixed by the canonical Galois action after field extension. -/
noncomputable def galoisFixedSubgroup
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    AddSubgroup (FieldExtension.baseChange k K f).PicardGroup :=
  @FixedPoints.addSubgroup Gal(K/k) (FieldExtension.baseChange k K f).PicardGroup
    inferInstance inferInstance (galoisAction k K f)

/-- A Picard class lies in the Galois-fixed subgroup exactly when every Galois element fixes
it under the canonical action. -/
theorem mem_galoisFixedSubgroup
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (x : (FieldExtension.baseChange k K f).PicardGroup) :
    x ∈ galoisFixedSubgroup k K f ↔
      ∀ σ : Gal(K/k), (galoisAction k K f).toMulAction.toSMul.smul σ x = x := sorry

/-- The joint canonical Galois action on the Picard group equipped with the discrete topology. -/
noncomputable def galoisActionMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Gal(K/k) × WithDiscreteTopology (FieldExtension.baseChange k K f).PicardGroup →
      WithDiscreteTopology (FieldExtension.baseChange k K f).PicardGroup :=
  fun p ↦ (WithTopology.equiv _ ⊥).symm
    ((galoisAction k K f).toMulAction.toSMul.smul p.1 (WithTopology.equiv _ ⊥ p.2))

end AlgebraicGeometry.FieldExtension.Picard
