/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Associativity
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed.Currying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived currying carried by a closed comparison

This leaf specializes the generic fixed-right currying owner to an `RHom.ClosedComparison`.
It preserves the concrete `rightAdjointUniq` choice and its agreement with the canonical
objectwise tensor-source isomorphism; no local closed or monoidal instance is reconstructed.

@stack 0A65
@stack 03EO
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [BraidedCategory (DerivedCategory (ModuleCat A))]
variable [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]

local notation "D(" A ")" => DerivedCategory (ModuleCat A)

/-- The bundled composite adjunction whose right adjoint is iterated selected internal Hom. -/
@[stacks 0A65 "bundled composite derived tensor/internal-Hom adjunction"]
noncomputable abbrev derivedInternalHomTensorCompositeAdjunction
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    (DerivedTensor.Right.functor K ⋙ DerivedTensor.Right.functor L) ⊣
      (MonoidalClosed.ihomOf P.closed L ⋙ MonoidalClosed.ihomOf P.closed K) :=
  DerivedTensor.Right.Closed.Currying.compositeAdjunctionOf
    P.closed P.tensorModel K L

/-- The bundled composite adjunction transported through derived tensor associativity. -/
@[stacks 0A65 "bundled transported composite derived tensor adjunction"]
noncomputable abbrev derivedInternalHomTensorComparisonAdjunction
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    DerivedTensor.Right.functor (DerivedTensor.Right.obj K L) ⊣
      (MonoidalClosed.ihomOf P.closed L ⋙ MonoidalClosed.ihomOf P.closed K) :=
  DerivedTensor.Right.Closed.Currying.comparisonAdjunctionOf
    P.closed P.tensorModel K L

/-- The bundled functor-level selected internal-Hom currying isomorphism. -/
@[stacks 0A65 "bundled derived internal-Hom currying natural isomorphism"]
noncomputable abbrev derivedInternalHomTensorNatIso
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    MonoidalClosed.ihomOf P.closed L ⋙ MonoidalClosed.ihomOf P.closed K ≅
      MonoidalClosed.ihomOf P.closed (DerivedTensor.Right.obj K L) :=
  DerivedTensor.Right.Closed.Currying.natIsoOf P.closed P.tensorModel K L

/-- The bundled objectwise selected internal-Hom currying isomorphism. -/
@[stacks 0A65 "bundled derived internal-Hom currying object isomorphism"]
noncomputable abbrev derivedInternalHomTensorIso
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    (MonoidalClosed.ihomOf P.closed K).obj
        ((MonoidalClosed.ihomOf P.closed L).obj M) ≅
      (MonoidalClosed.ihomOf P.closed (DerivedTensor.Right.obj K L)).obj M :=
  DerivedTensor.Right.Closed.Currying.isoOf P.closed P.tensorModel K L M

/-- The bundled currying NatIso is the comparison of the two named right adjoints. -/
@[simp, stacks 0A65 "bundled currying right-adjoint uniqueness specification"]
theorem derivedInternalHomTensorNatIso_eq_rightAdjointUniq
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    P.derivedInternalHomTensorNatIso K L =
      (P.derivedInternalHomTensorComparisonAdjunction K L).rightAdjointUniq
        (P.selectedAdjunction (DerivedTensor.Right.obj K L)) :=
  DerivedTensor.Right.Closed.Currying.natIsoOf_eq_rightAdjointUniq
    P.closed P.tensorModel K L

/-- Taking the mate of the bundled forward component recovers the transported counit. -/
@[stacks 0A65 "bundled derived currying mate specification"]
theorem derivedInternalHomTensorNatIso_homEquiv_symm
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    ((P.selectedAdjunction (DerivedTensor.Right.obj K L)).homEquiv _ _).symm
        ((P.derivedInternalHomTensorNatIso K L).hom.app M) =
      (P.derivedInternalHomTensorComparisonAdjunction K L).counit.app M :=
  DerivedTensor.Right.Closed.Currying.natIsoOf_homEquiv_symm
    P.closed P.tensorModel K L M

/-- Postcomposition with bundled currying transports a transpose to the composite adjunction. -/
@[stacks 0A65 "bundled derived currying transpose transport"]
theorem derivedInternalHomTensorNatIso_homEquiv_symm_comp
    (P : RHom.ClosedComparison (A := A)) (K L : D(A))
    {X M : D(A)}
    (φ : X ⟶ (MonoidalClosed.ihomOf P.closed L ⋙
      MonoidalClosed.ihomOf P.closed K).obj M) :
    ((P.selectedAdjunction (DerivedTensor.Right.obj K L)).homEquiv X M).symm
        (φ ≫ (P.derivedInternalHomTensorNatIso K L).hom.app M) =
      ((P.derivedInternalHomTensorComparisonAdjunction K L).homEquiv X M).symm φ :=
  DerivedTensor.Right.Closed.Currying.natIsoOf_homEquiv_symm_comp
    P.closed P.tensorModel K L φ

/-- The bundled functor-level currying comparison is natural in its target. -/
@[reassoc, stacks 03EO "bundled derived currying target naturality"]
theorem derivedInternalHomTensorNatIso_hom_naturality
    (P : RHom.ClosedComparison (A := A)) (K L : D(A))
    {M₁ M₂ : D(A)} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf P.closed L ⋙ MonoidalClosed.ihomOf P.closed K).map f ≫
        (P.derivedInternalHomTensorNatIso K L).hom.app M₂ =
      (P.derivedInternalHomTensorNatIso K L).hom.app M₁ ≫
        (MonoidalClosed.ihomOf P.closed (DerivedTensor.Right.obj K L)).map f :=
  DerivedTensor.Right.Closed.Currying.natIsoOf_hom_naturality
    P.closed P.tensorModel K L f

/-- The inverse bundled functor-level currying comparison is natural in its target. -/
@[reassoc, stacks 03EO "inverse bundled derived currying target naturality"]
theorem derivedInternalHomTensorNatIso_inv_naturality
    (P : RHom.ClosedComparison (A := A)) (K L : D(A))
    {M₁ M₂ : D(A)} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf P.closed (DerivedTensor.Right.obj K L)).map f ≫
        (P.derivedInternalHomTensorNatIso K L).inv.app M₂ =
      (P.derivedInternalHomTensorNatIso K L).inv.app M₁ ≫
        (MonoidalClosed.ihomOf P.closed L ⋙ MonoidalClosed.ihomOf P.closed K).map f :=
  DerivedTensor.Right.Closed.Currying.natIsoOf_inv_naturality
    P.closed P.tensorModel K L f

/-- The bundled functor-level comparison has the canonical concrete object component. -/
@[simp, stacks 0A65 "bundled derived currying component agreement"]
theorem derivedInternalHomTensorNatIso_app
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    (P.derivedInternalHomTensorNatIso K L).app M =
      P.derivedInternalHomTensorIso K L M :=
  DerivedTensor.Right.Closed.Currying.natIsoOf_app
    P.closed P.tensorModel K L M

/-- The inverse bundled component agrees with the inverse objectwise isomorphism. -/
@[simp, stacks 0A65 "inverse bundled derived currying component agreement"]
theorem derivedInternalHomTensorNatIso_inv_app
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    (P.derivedInternalHomTensorNatIso K L).inv.app M =
      (P.derivedInternalHomTensorIso K L M).inv :=
  DerivedTensor.Right.Closed.Currying.natIsoOf_inv_app
    P.closed P.tensorModel K L M

/-- Bundled currying is contravariantly natural in its left tensor factor. -/
@[reassoc, stacks 03EO "bundled derived currying left naturality"]
theorem derivedInternalHomTensorIso_natural_left
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L M : D(A)} (f : K₁ ⟶ K₂) :
    (MonoidalClosed.preOf P.closed f).app
          ((MonoidalClosed.ihomOf P.closed L).obj M) ≫
        (P.derivedInternalHomTensorIso K₁ L M).hom =
      (P.derivedInternalHomTensorIso K₂ L M).hom ≫
        (MonoidalClosed.preOf P.closed
          ((DerivedTensor.Right.functor L).map f)).app M :=
  DerivedTensor.Right.Closed.Currying.isoOf_natural_left
    P.closed P.tensorModel f

/-- Bundled currying is contravariantly natural in its middle tensor factor. -/
@[reassoc, stacks 03EO "bundled derived currying middle naturality"]
theorem derivedInternalHomTensorIso_natural_middle
    (P : RHom.ClosedComparison (A := A))
    (K : D(A)) {L₁ L₂ M : D(A)} (f : L₁ ⟶ L₂) :
    (MonoidalClosed.ihomOf P.closed K).map
          ((MonoidalClosed.preOf P.closed f).app M) ≫
        (P.derivedInternalHomTensorIso K L₁ M).hom =
      (P.derivedInternalHomTensorIso K L₂ M).hom ≫
        (MonoidalClosed.preOf P.closed
          ((P.derivedTensorProductMap f).app K)).app M :=
  DerivedTensor.Right.Closed.Currying.isoOf_natural_middle
    P.closed P.tensorModel K f

/-- Bundled currying is covariantly natural in its target. -/
@[reassoc, stacks 03EO "bundled derived currying target object naturality"]
theorem derivedInternalHomTensorIso_natural_right
    (P : RHom.ClosedComparison (A := A))
    (K L : D(A)) {M₁ M₂ : D(A)} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf P.closed K).map
          ((MonoidalClosed.ihomOf P.closed L).map f) ≫
        (P.derivedInternalHomTensorIso K L M₂).hom =
      (P.derivedInternalHomTensorIso K L M₁).hom ≫
        (MonoidalClosed.ihomOf P.closed (DerivedTensor.Right.obj K L)).map f :=
  DerivedTensor.Right.Closed.Currying.isoOf_natural_right
    P.closed P.tensorModel K L f

/-- The inverse bundled currying is natural in its left tensor factor. -/
@[reassoc, stacks 03EO "inverse bundled derived currying left naturality"]
theorem derivedInternalHomTensorIso_inv_natural_left
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L M : D(A)} (f : K₁ ⟶ K₂) :
    (MonoidalClosed.preOf P.closed
        ((DerivedTensor.Right.functor L).map f)).app M ≫
        (P.derivedInternalHomTensorIso K₁ L M).inv =
      (P.derivedInternalHomTensorIso K₂ L M).inv ≫
        (MonoidalClosed.preOf P.closed f).app
          ((MonoidalClosed.ihomOf P.closed L).obj M) :=
  DerivedTensor.Right.Closed.Currying.isoOf_inv_natural_left
    P.closed P.tensorModel f

/-- The inverse bundled currying is natural in its middle tensor factor. -/
@[reassoc, stacks 03EO "inverse bundled derived currying middle naturality"]
theorem derivedInternalHomTensorIso_inv_natural_middle
    (P : RHom.ClosedComparison (A := A))
    (K : D(A)) {L₁ L₂ M : D(A)} (f : L₁ ⟶ L₂) :
    (MonoidalClosed.preOf P.closed ((P.derivedTensorProductMap f).app K)).app M ≫
        (P.derivedInternalHomTensorIso K L₁ M).inv =
      (P.derivedInternalHomTensorIso K L₂ M).inv ≫
        (MonoidalClosed.ihomOf P.closed K).map
          ((MonoidalClosed.preOf P.closed f).app M) :=
  DerivedTensor.Right.Closed.Currying.isoOf_inv_natural_middle
    P.closed P.tensorModel K f

/-- The inverse bundled currying is natural in its target. -/
@[reassoc, stacks 03EO "inverse bundled derived currying target naturality"]
theorem derivedInternalHomTensorIso_inv_natural_right
    (P : RHom.ClosedComparison (A := A))
    (K L : D(A)) {M₁ M₂ : D(A)} (f : M₁ ⟶ M₂) :
    (MonoidalClosed.ihomOf P.closed (DerivedTensor.Right.obj K L)).map f ≫
        (P.derivedInternalHomTensorIso K L M₂).inv =
      (P.derivedInternalHomTensorIso K L M₁).inv ≫
        (MonoidalClosed.ihomOf P.closed K).map
          ((MonoidalClosed.ihomOf P.closed L).map f) :=
  DerivedTensor.Right.Closed.Currying.isoOf_inv_natural_right
    P.closed P.tensorModel K L f

end CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison
