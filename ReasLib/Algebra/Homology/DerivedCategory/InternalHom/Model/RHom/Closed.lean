/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed comparisons for canonical module RHom

This leaf contains only the optional compatibility gate between canonical module `RHom` and an
ambient closed owner.  The canonical object and its projective computations live in
`InternalHom.Model.RHom`, so users that do not need an ambient tensor comparison can import the
lighter owner directly.

This compatibility leaf uses `ModuleCat.{u} A` for `A : Type u`: Mathlib's module tensor and
closed instances currently impose that same-universe presentation.  The short canonical `RHom`
facade has the same boundary; carrier-polymorphic consumers use the separate `RHom.At` or generic
enriched owner until the corresponding closed/tensor structures are available at that universe.

@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped _root_.DerivedInternalHom

namespace CategoryTheory.DerivedCategory.InternalHom.RHom

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- Pointwise adjunction data identifying canonical `RHom` as the right adjoint of canonical
fixed-right derived tensoring.  This is explicit ordinary data, not a global instance. -/
@[stacks 0E1U "canonical derived tensor-RHom adjunction family"]
abbrev TensorAdjunction [Has (A := A)] :=
  (K : DerivedCategory (ModuleCat.{u} A)) →
    DerivedTensor.Right.functor K ⊣ targetFunctor (A := A) K

/-- The data needed to compare canonical module `RHom` with one selected closed owner.  The
closed structure, ambient tensor model, and canonical tensor-`RHom` adjunction remain observable
fields; no compatibility datum is reconstructed through typeclass search. -/
@[stacks 0E1U "closed presentation of canonical module RHom"]
structure ClosedComparison [Has (A := A)] where
  /-- The selected ambient closed structure. -/
  closed : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))
  /-- The explicit model comparing canonical derived tensoring with ambient tensoring. -/
  tensorModel : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
    (C := ModuleCat.{u} A)
  /-- The pointwise adjunction exhibiting canonical `RHom` as the right adjoint of canonical
  fixed-right derived tensoring. -/
  adjunction : TensorAdjunction (A := A)

/-- Construct a closed comparison from its selected closed structure, tensor model, and
adjunction family. -/
noncomputable def ClosedComparison.of [Has (A := A)]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} A))
    (adj : TensorAdjunction (A := A)) :
    ClosedComparison (A := A) :=
  ⟨H, T, adj⟩

/-- The fields of a constructed closed comparison are the supplied closed structure, tensor
model, and adjunction family. -/
theorem ClosedComparison.of_spec [Has (A := A)]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} A))
    (adj : TensorAdjunction (A := A)) :
    (ClosedComparison.of H T adj).closed = H ∧
      (ClosedComparison.of H T adj).tensorModel = T ∧
        (ClosedComparison.of H T adj).adjunction = adj := sorry

section Selected

variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]

/-- Canonical `RHom(K, -)` and the internal Hom selected by `H` are naturally isomorphic once
their left adjoints are related by an ambient tensor model. -/
@[stacks 0E1U "canonical RHom to selected internal-Hom comparison"]
noncomputable def targetFunctorIsoIhom [Has (A := A)]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} A))
    (adj : TensorAdjunction (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    targetFunctor (A := A) K ≅ MonoidalClosed.ihomOf H K :=
  (adj K).rightAdjointUniq (DerivedTensor.Right.Closed.adjunctionOf H T K)

/-- The objectwise canonical comparison from `RHom_A(K, L)` to the internal Hom selected by `H`. -/
@[stacks 0E1U "canonical RHom object to selected internal-Hom object"]
noncomputable abbrev objIsoIhom [Has (A := A)]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} A))
    (adj : TensorAdjunction (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    obj (A := A) K L ≅ InternalHom.obj H K L :=
  (targetFunctorIsoIhom H T adj K).app L

/-- The forward natural transformation of the canonical `RHom` comparison is the uniqueness map
between the two right adjoints. -/
@[simp, stacks 0E1U "canonical RHom comparison forward map"]
theorem targetFunctorIsoIhom_hom [Has (A := A)]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} A))
    (adj : TensorAdjunction (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (targetFunctorIsoIhom H T adj K).hom =
      ((adj K).rightAdjointUniq
        (DerivedTensor.Right.Closed.adjunctionOf H T K)).hom := rfl

/-- The inverse natural transformation of the canonical `RHom` comparison is the inverse
right-adjoint uniqueness map. -/
@[simp, stacks 0E1U "canonical RHom comparison inverse map"]
theorem targetFunctorIsoIhom_inv [Has (A := A)]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} A))
    (adj : TensorAdjunction (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (targetFunctorIsoIhom H T adj K).inv =
      ((adj K).rightAdjointUniq
        (DerivedTensor.Right.Closed.adjunctionOf H T K)).inv := rfl

namespace ClosedComparison

/-- The functor-level comparison carried by a bundled closed presentation of canonical `RHom`. -/
@[stacks 0E1U "bundled canonical RHom functor comparison"]
noncomputable abbrev targetIso [Has (A := A)]
    (M : ClosedComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    targetFunctor (A := A) K ≅ MonoidalClosed.ihomOf M.closed K :=
  targetFunctorIsoIhom M.closed M.tensorModel M.adjunction K

/-- The objectwise comparison carried by a bundled closed presentation of canonical `RHom`. -/
@[stacks 0E1U "bundled canonical RHom object comparison"]
noncomputable abbrev objIso [Has (A := A)]
    (M : ClosedComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    obj (A := A) K L ≅ InternalHom.obj M.closed K L :=
  (M.targetIso K).app L

end ClosedComparison

end Selected

end CategoryTheory.DerivedCategory.InternalHom.RHom

namespace CochainComplex.ProjectiveMinus

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]

/-- A projective-minus source computes the internal Hom selected by a closed comparison of
canonical `RHom`. -/
@[stacks 0E1U "projective-minus model for selected derived internal Hom"]
theorem representsInternalHom
    [RHom.Has (A := A)] (M : RHom.ClosedComparison (A := A))
    (P : CochainComplex.ProjectiveMinus (ModuleCat.{u} A))
    (F : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex A P F))
      (RHom[M.closed](DerivedCategory.Q.obj P, DerivedCategory.Q.obj F)) := by
  rcases CochainComplex.ProjectiveMinus.representsRHom P F with ⟨e⟩
  exact ⟨e ≪≫ M.objIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)⟩

/-- The finite-projective specialization of the selected internal-Hom computation retains its
bundled closed comparison. -/
@[stacks 0E1U "finite-projective model for selected derived internal Hom"]
theorem representsInternalHom_of_finiteProjective
    [RHom.Has (A := A)] (M : RHom.ClosedComparison (A := A))
    (P F : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : CochainComplex.minus (ModuleCat.{u} A) P)
    (hPfp : P.IsTermwiseFiniteProjective) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex A P F))
      (RHom[M.closed](DerivedCategory.Q.obj P, DerivedCategory.Q.obj F)) := by
  rcases CochainComplex.ProjectiveMinus.representsRHom_of_finiteProjective
    P F hP hPfp with ⟨e⟩
  exact ⟨e ≪≫ M.objIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)⟩

/-- The selected internal-Hom computation transports across explicit representative
isomorphisms while retaining its bundled canonical `RHom` compatibility gate. -/
@[stacks 0E1U "selected internal-Hom model after representative transport"]
theorem representsInternalHom_of_models
    [RHom.Has (A := A)] (M : RHom.ClosedComparison (A := A))
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat.{u} A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat.{u} A) P)
    (hPfp : P.IsTermwiseFiniteProjective) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex A P F))
      (RHom[M.closed](K, L)) := by
  rcases CochainComplex.ProjectiveMinus.representsRHom_of_models
    P F eP eF hP hPfp with ⟨e⟩
  exact ⟨e ≪≫ M.objIso K L⟩

end CochainComplex.ProjectiveMinus
