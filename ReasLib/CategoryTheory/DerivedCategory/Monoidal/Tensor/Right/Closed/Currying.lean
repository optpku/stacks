module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Associativity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Currying for fixed-right derived tensoring

This leaf owns the functor-level currying comparison determined by an explicit closed structure
and fixed-right tensor model.  The comparison is the uniqueness isomorphism between two named
right adjoints; its object components agree with the existing concrete tensor-source isomorphism.
No closed structure, tensor model, or parametrized adjunction is installed as an instance.

@stack 0A65
@stack 03EO
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Right.Closed.Currying

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ K L : CochainComplex C ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [MonoidalCategory (DerivedCategory C)] [BraidedCategory (DerivedCategory C)]
variable [DerivedTensor.Right.Has (C := C)]

local notation "D" => DerivedCategory C

/-- The composite fixed-right adjunction whose right adjoint is iterated selected internal Hom. -/
@[stacks 0A65 "composite derived tensor/internal-Hom adjunction"]
noncomputable abbrev compositeAdjunctionOf
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L : D) :
    (DerivedTensor.Right.functor K ⋙ DerivedTensor.Right.functor L) ⊣
      (MonoidalClosed.ihomOf H L ⋙ MonoidalClosed.ihomOf H K) :=
  (DerivedTensor.Right.Closed.adjunctionOf H T K).comp
    (DerivedTensor.Right.Closed.adjunctionOf H T L)

/-- Transport the composite adjunction through the model-parametrized tensor associator. -/
@[stacks 0A65 "transported composite derived tensor adjunction"]
noncomputable abbrev comparisonAdjunctionOf
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L : D) :
    DerivedTensor.Right.functor (DerivedTensor.Right.obj K L) ⊣
      (MonoidalClosed.ihomOf H L ⋙ MonoidalClosed.ihomOf H K) :=
  (compositeAdjunctionOf H T K L).ofNatIsoLeft
    (DerivedTensor.Right.tensorAssoc T K L)

/-- The functor-level selected currying isomorphism obtained by right-adjoint uniqueness. -/
@[stacks 0A65 "derived internal-Hom currying natural isomorphism"]
noncomputable def natIsoOf
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L : D) :
    MonoidalClosed.ihomOf H L ⋙ MonoidalClosed.ihomOf H K ≅
      MonoidalClosed.ihomOf H (DerivedTensor.Right.obj K L) :=
  (comparisonAdjunctionOf H T K L).rightAdjointUniq
    (DerivedTensor.Right.Closed.adjunctionOf H T (DerivedTensor.Right.obj K L))

/-- The currying NatIso is definitionally selected by the two named right adjoints. -/
@[simp, stacks 0A65 "derived currying right-adjoint uniqueness specification"]
theorem natIsoOf_eq_rightAdjointUniq
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L : D) :
    natIsoOf H T K L =
      (comparisonAdjunctionOf H T K L).rightAdjointUniq
        (DerivedTensor.Right.Closed.adjunctionOf H T
          (DerivedTensor.Right.obj K L)) := rfl

/-- Taking the mate of the forward currying component recovers the transported counit. -/
@[stacks 0A65 "derived currying mate specification"]
theorem natIsoOf_homEquiv_symm
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L M : D) :
    ((DerivedTensor.Right.Closed.adjunctionOf H T
        (DerivedTensor.Right.obj K L)).homEquiv _ _).symm
        ((natIsoOf H T K L).hom.app M) =
      (comparisonAdjunctionOf H T K L).counit.app M :=
  Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (comparisonAdjunctionOf H T K L)
    (DerivedTensor.Right.Closed.adjunctionOf H T
      (DerivedTensor.Right.obj K L)) M

/-- Postcomposition with currying transports a transpose to the composite adjunction. -/
@[stacks 0A65 "derived currying transpose transport"]
theorem natIsoOf_homEquiv_symm_comp
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L : D)
    {A M : D}
    (φ : A ⟶ (MonoidalClosed.ihomOf H L ⋙ MonoidalClosed.ihomOf H K).obj M) :
    ((DerivedTensor.Right.Closed.adjunctionOf H T
        (DerivedTensor.Right.obj K L)).homEquiv A M).symm
        (φ ≫ (natIsoOf H T K L).hom.app M) =
      ((comparisonAdjunctionOf H T K L).homEquiv A M).symm φ := by
  rw [(DerivedTensor.Right.Closed.adjunctionOf H T
    (DerivedTensor.Right.obj K L)).homEquiv_naturality_left_symm]
  rw [natIsoOf_homEquiv_symm]
  symm
  simpa only [Category.comp_id, Adjunction.homEquiv_symm_id] using
    (comparisonAdjunctionOf H T K L).homEquiv_naturality_left_symm φ (𝟙 _)

/-- The forward functor-level currying comparison is natural in its target. -/
@[reassoc, stacks 03EO "derived currying target naturality"]
theorem natIsoOf_hom_naturality
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L : D)
    {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf H L ⋙ MonoidalClosed.ihomOf H K).map f ≫
        (natIsoOf H T K L).hom.app M₂ =
      (natIsoOf H T K L).hom.app M₁ ≫
        (MonoidalClosed.ihomOf H (DerivedTensor.Right.obj K L)).map f :=
  (natIsoOf H T K L).hom.naturality f

/-- The inverse functor-level currying comparison is natural in its target. -/
@[reassoc, stacks 03EO "inverse derived currying target naturality"]
theorem natIsoOf_inv_naturality
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L : D)
    {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf H (DerivedTensor.Right.obj K L)).map f ≫
        (natIsoOf H T K L).inv.app M₂ =
      (natIsoOf H T K L).inv.app M₁ ≫
        (MonoidalClosed.ihomOf H L ⋙ MonoidalClosed.ihomOf H K).map f :=
  (natIsoOf H T K L).inv.naturality f

/-- The concrete objectwise currying isomorphism determined by `H` and `T`. -/
@[stacks 0A65 "derived internal-Hom currying object isomorphism"]
noncomputable abbrev isoOf
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L M : D) :
    (MonoidalClosed.ihomOf H K).obj ((MonoidalClosed.ihomOf H L).obj M) ≅
      (MonoidalClosed.ihomOf H (DerivedTensor.Right.obj K L)).obj M :=
  DerivedTensor.Right.Closed.InternalHomTensor.isoOf H T K L M

/-- The objectwise currying isomorphism is ambient closed currying followed by model transport. -/
@[simp, stacks 0A65 "derived internal-Hom currying object specification"]
theorem isoOf_spec
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L M : D) :
    isoOf H T K L M =
      MonoidalClosed.InternalHomTensor.isoOf H K L M ≪≫
        MonoidalClosed.internalHomMapIsoOf H
          (DerivedTensor.Right.Monoidal.Model.objIsoTensor T K L) (Iso.refl M) :=
  DerivedTensor.Right.Closed.InternalHomTensor.isoOf_spec H T K L M

/-- The right-adjoint-uniqueness NatIso has the canonical concrete object component. -/
@[simp, stacks 0A65 "derived currying component agreement"]
theorem natIsoOf_app
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L M : D) :
    (natIsoOf H T K L).app M = isoOf H T K L M := sorry

/-- The inverse NatIso component agrees with the inverse concrete objectwise isomorphism. -/
@[simp, stacks 0A65 "inverse derived currying component agreement"]
theorem natIsoOf_inv_app
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C)) (K L M : D) :
    (natIsoOf H T K L).inv.app M = (isoOf H T K L M).inv := by
  exact congrArg Iso.inv (natIsoOf_app H T K L M)

/-- Currying is contravariantly natural in its left tensor factor. -/
@[reassoc, stacks 03EO "derived currying left naturality"]
theorem isoOf_natural_left
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C))
    {K₁ K₂ L M : D} (f : K₁ ⟶ K₂) :
    (MonoidalClosed.preOf H f).app ((MonoidalClosed.ihomOf H L).obj M) ≫
        (isoOf H T K₁ L M).hom =
      (isoOf H T K₂ L M).hom ≫
        (MonoidalClosed.preOf H ((DerivedTensor.Right.functor L).map f)).app M :=
  DerivedTensor.Right.Closed.InternalHomTensor.isoOf_natural_left H T f

/-- Currying is contravariantly natural in its middle tensor factor. -/
@[reassoc, stacks 03EO "derived currying middle naturality"]
theorem isoOf_natural_middle
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C))
    (K : D) {L₁ L₂ M : D} (f : L₁ ⟶ L₂) :
    (MonoidalClosed.ihomOf H K).map ((MonoidalClosed.preOf H f).app M) ≫
        (isoOf H T K L₁ M).hom =
      (isoOf H T K L₂ M).hom ≫
        (MonoidalClosed.preOf H
          ((DerivedTensor.Right.Closed.tensorMapOf H T f).app K)).app M :=
  DerivedTensor.Right.Closed.InternalHomTensor.isoOf_natural_middle H T K f

/-- Currying is covariantly natural in its target. -/
@[reassoc, stacks 03EO "derived currying target object naturality"]
theorem isoOf_natural_right
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C))
    (K L : D) {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf H K).map ((MonoidalClosed.ihomOf H L).map f) ≫
        (isoOf H T K L M₂).hom =
      (isoOf H T K L M₁).hom ≫
        (MonoidalClosed.ihomOf H (DerivedTensor.Right.obj K L)).map f :=
  DerivedTensor.Right.Closed.InternalHomTensor.isoOf_natural_right H T K L f

/-- The inverse currying isomorphism is natural in its left tensor factor. -/
@[reassoc, stacks 03EO "inverse derived currying left naturality"]
theorem isoOf_inv_natural_left
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C))
    {K₁ K₂ L M : D} (f : K₁ ⟶ K₂) :
    (MonoidalClosed.preOf H ((DerivedTensor.Right.functor L).map f)).app M ≫
        (isoOf H T K₁ L M).inv =
      (isoOf H T K₂ L M).inv ≫
        (MonoidalClosed.preOf H f).app ((MonoidalClosed.ihomOf H L).obj M) := by
  rw [Iso.comp_inv_eq (isoOf H T K₁ L M), Category.assoc,
    Iso.eq_inv_comp (isoOf H T K₂ L M)]
  exact (isoOf_natural_left H T f).symm

/-- The inverse currying isomorphism is natural in its middle tensor factor. -/
@[reassoc, stacks 03EO "inverse derived currying middle naturality"]
theorem isoOf_inv_natural_middle
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C))
    (K : D) {L₁ L₂ M : D} (f : L₁ ⟶ L₂) :
    (MonoidalClosed.preOf H
        ((DerivedTensor.Right.Closed.tensorMapOf H T f).app K)).app M ≫
        (isoOf H T K L₁ M).inv =
      (isoOf H T K L₂ M).inv ≫
        (MonoidalClosed.ihomOf H K).map ((MonoidalClosed.preOf H f).app M) := by
  rw [Iso.comp_inv_eq (isoOf H T K L₁ M), Category.assoc,
    Iso.eq_inv_comp (isoOf H T K L₂ M)]
  exact (isoOf_natural_middle H T K f).symm

/-- The inverse currying isomorphism is natural in its target. -/
@[reassoc, stacks 03EO "inverse derived currying target naturality"]
theorem isoOf_inv_natural_right
    (H : MonoidalClosed D)
    (T : DerivedTensor.Right.Monoidal.Model (C := C))
    (K L : D) {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf H (DerivedTensor.Right.obj K L)).map f ≫
        (isoOf H T K L M₂).inv =
      (isoOf H T K L M₁).inv ≫
        (MonoidalClosed.ihomOf H K).map ((MonoidalClosed.ihomOf H L).map f) := by
  rw [Iso.comp_inv_eq (isoOf H T K L M₂), Category.assoc,
    Iso.eq_inv_comp (isoOf H T K L M₁)]
  exact (isoOf_natural_right H T K L f).symm

end CategoryTheory.DerivedCategory.DerivedTensor.Right.Closed.Currying
