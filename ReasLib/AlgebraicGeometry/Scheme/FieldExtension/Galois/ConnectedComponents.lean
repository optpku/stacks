/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic

/-!
# Galois actions on connected components after field extension

The canonical actions use the inverse on `Gal(K / k)` and the direct element
on its opposite.  This records the contravariant nature of `Spec` once, so
applications can use the ordinary `•` notation without rebuilding pullback
maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Connected

/-- The canonical left `Gal(K / k)` action on connected components of a field-extension
base change. -/
noncomputable instance instMulAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MulAction Gal(K/k) (ConnectedComponents (FieldExtension.baseChange k K f)) where
  smul σ :=
    Continuous.connectedComponentsMap
      ((FieldExtension.Galois.aut k K f σ.symm).hom.continuous)
  one_smul := sorry
  mul_smul := sorry

/-- Computation rule for the canonical `Gal(K / k)` action on connected components. -/
theorem smul_def
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : Gal(K/k)) (C : ConnectedComponents (FieldExtension.baseChange k K f)) :
    σ • C =
      Continuous.connectedComponentsMap
        ((FieldExtension.Galois.aut k K f σ.symm).hom.continuous) C := sorry

/-- The canonical left action of the opposite Galois group on connected components, with no
inverse hidden in the input element. -/
noncomputable instance instOppositeMulAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MulAction (Gal(K/k))ᵐᵒᵖ (ConnectedComponents (FieldExtension.baseChange k K f)) where
  smul σ :=
    Continuous.connectedComponentsMap
      ((FieldExtension.Galois.aut k K f σ.unop).hom.continuous)
  one_smul := sorry
  mul_smul := sorry

/-- Computation rule for the opposite-Galois action on connected components. -/
theorem op_smul_def
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : (Gal(K/k))ᵐᵒᵖ)
    (C : ConnectedComponents (FieldExtension.baseChange k K f)) :
    σ • C =
      Continuous.connectedComponentsMap
        ((FieldExtension.Galois.aut k K f σ.unop).hom.continuous) C := sorry

end FieldExtension.Galois.Connected

end AlgebraicGeometry
