/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Bifunctor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Bifunctor
public import ReasLib.CategoryTheory.Adjunction.Parametrized.Localization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Parametrized Derived Tensor-Hom Adjunction

This leaf upgrades the fixed-strict-bimodule derived tensor-Hom adjunction to a parametrized
adjunction over the full derived category of bimodules.  Choosing a strict representative is
confined to the construction of the pointwise adjunction; downstream users work with the
derived-bimodule parameter itself.  The adjunction-facing layer intentionally uses the common
carrier universe required by the current internal-Hom owner; the tensor-only bifunctor remains
available at independent carrier universes in `Tensor.derivedBifunctor`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v w x

namespace DifferentialGradedBimodule.TensorHom.Derived

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- The fixed-bimodule derived tensor-Hom adjunctions, assembled functorially over strict DG
bimodules before localizing the parameter. -/
@[stacks 09LT "strictly parametrized derived tensor-Hom adjunction"]
noncomputable def strictParametrizedAdjunction
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    Tensor.derivedBimoduleFunctor.{u, v, v, w, x} A B ⊣₂
      InternalHom.derivedBimoduleFunctor.{u, v, w, x} A B :=
  ParametrizedAdjunction.mk'
    (fun N ↦ TensorHom.derivedAdjunction N)
    (fun {_ _} f {M} {P} g ↦
      TensorHom.derivedHomEquiv_naturality_middle f M P g)

/-- The fixed-strict-bimodule derived adjunction, transported to the corresponding object of
the full derived bimodule category. -/
@[stacks 09LT "derived tensor-Hom adjunction at a strict bimodule object"]
noncomputable def strictAdjunction (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Tensor.derivedBifunctor A B).obj
        (DifferentialGradedBimodule.Derived.object N) ⊣
      (InternalHom.derivedBifunctor A B).obj
        (op (DifferentialGradedBimodule.Derived.object N)) :=
  (strictParametrizedAdjunction.{u, v, w, x} A B).localizationOnImage
    (L := DifferentialGradedBimodule.Derived.fromBimodules.{u, v, w, x} A B)
    (W := DifferentialGradedBimodule.quasiIso A B)
    (F' := Tensor.derivedBifunctor A B)
    (G' := InternalHom.derivedBifunctor A B) N

/-- Currying through `strictAdjunction` agrees with fixed-bimodule derived currying after the
canonical strict-image comparisons. -/
@[simp, stacks 09LT "strict-image formula for derived tensor-Hom currying"]
theorem strictAdjunction_homEquiv_apply
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (f : ((Tensor.derivedBifunctor A B).obj
      (DifferentialGradedBimodule.Derived.object N)).obj M ⟶ P) :
    (strictAdjunction N).homEquiv M P f =
      TensorHom.derivedHomEquiv N M P
          ((Tensor.derivedBifunctorObjIso N).inv.app M ≫ f) ≫
        (InternalHom.derivedBifunctorObjIso N).inv.app P := sorry

/-- Uncurrying through `strictAdjunction` agrees with fixed-bimodule derived uncurrying after
the canonical strict-image comparisons. -/
@[simp, stacks 09LT "strict-image formula for derived tensor-Hom uncurrying"]
theorem strictAdjunction_homEquiv_symm_apply
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : M ⟶ ((InternalHom.derivedBifunctor A B).obj
      (op (DifferentialGradedBimodule.Derived.object N))).obj P) :
    ((strictAdjunction N).homEquiv M P).symm g =
      (Tensor.derivedBifunctorObjIso N).hom.app M ≫
        (TensorHom.derivedHomEquiv N M P).symm
          (g ≫ (InternalHom.derivedBifunctorObjIso N).hom.app P) := sorry

/-- Lemma 22.33.5 (09LT): derived tensor and derived internal Hom form an adjunction
parametrized by the full derived category of DG bimodules. -/
@[stacks 09LT "parametrized derived tensor-Hom adjunction"]
noncomputable def parametrizedAdjunction
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    Tensor.derivedBifunctor.{u, v, v, w, x} A B ⊣₂
      InternalHom.derivedBifunctor.{u, v, w, x} A B :=
  (strictParametrizedAdjunction.{u, v, w, x} A B).localization
    (L := DifferentialGradedBimodule.Derived.fromBimodules.{u, v, w, x} A B)
    (W := DifferentialGradedBimodule.quasiIso.{u, v, w, x} A B)
    (F' := Tensor.derivedBifunctor.{u, v, v, w, x} A B)
    (G' := InternalHom.derivedBifunctor.{u, v, w, x} A B)

/-- The derived tensor-Hom adjunction attached to an arbitrary derived bimodule. -/
@[stacks 09LT "derived tensor-Hom adjunction for a derived bimodule"]
noncomputable def adjunction
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B) :
    (Tensor.derivedBifunctor A B).obj K ⊣
      (InternalHom.derivedBifunctor A B).obj (op K) :=
  (parametrizedAdjunction.{u, v, w, x} A B).adj K

/-- The canonical shift structures on tensor and internal Hom are compatible with the
adjunction attached to an arbitrary derived bimodule. -/
@[stacks 09LT "shift-compatible tensor-Hom adjunction for a derived bimodule"]
instance adjunctionCommShift
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B) :
    (adjunction K).CommShift ℤ := sorry

/-- The tensor-Hom adjunction attached to an arbitrary derived bimodule is triangulated. -/
@[stacks 09LT "triangulated tensor-Hom adjunction for a derived bimodule"]
instance adjunctionIsTriangulated
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B) :
    (adjunction K).IsTriangulated := sorry

/-- The tensor-Hom equivalence attached to an arbitrary derived bimodule. -/
@[stacks 09LT "derived tensor-Hom equivalence for a derived bimodule"]
noncomputable def homEquiv
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B) :
    (((Tensor.derivedBifunctor A B).obj K).obj M ⟶ P) ≃
      (M ⟶ ((InternalHom.derivedBifunctor A B).obj (op K)).obj P) :=
  (adjunction K).homEquiv M P

/-- The tensor-Hom equivalence for a derived bimodule, with its canonical `R`-linear
structure. -/
@[stacks 09LT "linear derived tensor-Hom equivalence for a derived bimodule"]
noncomputable def homLinearEquiv
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B) :
    (((Tensor.derivedBifunctor A B).obj K).obj M ⟶ P) ≃ₗ[R]
      (M ⟶ ((InternalHom.derivedBifunctor A B).obj (op K)).obj P) :=
  (adjunction K).homLinearEquiv (k := R) M P

/-- The forward function of `homLinearEquiv` is derived currying. -/
@[simp, stacks 09LT "linear derived currying for a derived bimodule"]
theorem homLinearEquiv_apply
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (f : ((Tensor.derivedBifunctor A B).obj K).obj M ⟶ P) :
    homLinearEquiv K M P f = homEquiv K M P f := sorry

/-- The inverse function of `homLinearEquiv` is derived uncurrying. -/
@[simp, stacks 09LT "linear derived uncurrying for a derived bimodule"]
theorem homLinearEquiv_symm_apply
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : M ⟶ ((InternalHom.derivedBifunctor A B).obj (op K)).obj P) :
    (homLinearEquiv K M P).symm g = (homEquiv K M P).symm g := sorry

/-- Derived currying is natural in the derived bimodule parameter. -/
@[stacks 09LT "naturality of derived currying in a derived bimodule"]
theorem homEquiv_naturality_bimodule
    {K K' : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B}
    (f : K ⟶ K') (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : ((Tensor.derivedBifunctor A B).obj K').obj M ⟶ P) :
    homEquiv K M P (((Tensor.derivedBifunctor A B).map f).app M ≫ g) =
      homEquiv K' M P g ≫
        ((InternalHom.derivedBifunctor A B).map f.op).app P := sorry

/-- Derived uncurrying is natural in the derived bimodule parameter. -/
@[stacks 09LT "inverse naturality of derived currying in a derived bimodule"]
theorem homEquiv_naturality_bimodule_symm
    {K K' : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B}
    (f : K ⟶ K') (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : M ⟶ ((InternalHom.derivedBifunctor A B).obj (op K')).obj P) :
    (homEquiv K M P).symm
        (g ≫ ((InternalHom.derivedBifunctor A B).map f.op).app P) =
      ((Tensor.derivedBifunctor A B).map f).app M ≫
        (homEquiv K' M P).symm g := sorry

/-- Derived currying is natural in the tensor input. -/
@[stacks 09LT "naturality of derived currying in the tensor input"]
theorem homEquiv_naturality_left
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    {M M' : DifferentialGradedModule.Derived.Category.{u, v} A}
    (m : M ⟶ M') (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : ((Tensor.derivedBifunctor A B).obj K).obj M' ⟶ P) :
    homEquiv K M P (((Tensor.derivedBifunctor A B).obj K).map m ≫ g) =
      m ≫ homEquiv K M' P g := sorry

/-- Derived uncurrying is natural in the tensor input. -/
@[stacks 09LT "inverse naturality of derived currying in the tensor input"]
theorem homEquiv_naturality_left_symm
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    {M M' : DifferentialGradedModule.Derived.Category.{u, v} A}
    (m : M ⟶ M') (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : M' ⟶ ((InternalHom.derivedBifunctor A B).obj (op K)).obj P) :
    (homEquiv K M P).symm (m ≫ g) =
      ((Tensor.derivedBifunctor A B).obj K).map m ≫
        (homEquiv K M' P).symm g := sorry

/-- Derived currying is natural in the target. -/
@[stacks 09LT "naturality of derived currying in the target"]
theorem homEquiv_naturality_right
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    {P P' : DifferentialGradedModule.Derived.Category.{u, v} B}
    (p : P ⟶ P') (g : ((Tensor.derivedBifunctor A B).obj K).obj M ⟶ P) :
    homEquiv K M P' (g ≫ p) =
      homEquiv K M P g ≫
        ((InternalHom.derivedBifunctor A B).obj (op K)).map p := sorry

/-- Derived uncurrying is natural in the target. -/
@[stacks 09LT "inverse naturality of derived currying in the target"]
theorem homEquiv_naturality_right_symm
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    {P P' : DifferentialGradedModule.Derived.Category.{u, v} B}
    (p : P ⟶ P') (g : M ⟶ ((InternalHom.derivedBifunctor A B).obj (op K)).obj P) :
    (homEquiv K M P').symm
        (g ≫ ((InternalHom.derivedBifunctor A B).obj (op K)).map p) =
      (homEquiv K M P).symm g ≫ p := sorry

/-- On the derived image of a strict bimodule, the full parametrized adjunction recovers the
source-facing strict transport. -/
@[simp, stacks 09LT "parametrized derived tensor-Hom adjunction at a strict object"]
theorem adjunction_object
    (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    adjunction (DifferentialGradedBimodule.Derived.object N) =
      strictAdjunction N := sorry

/-- Currying in the full parametrized adjunction computes by fixed-bimodule derived currying
on a strict bimodule object. -/
@[simp, stacks 09LT "strict-object formula for parametrized derived currying"]
theorem homEquiv_object_apply
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (f : ((Tensor.derivedBifunctor A B).obj
      (DifferentialGradedBimodule.Derived.object N)).obj M ⟶ P) :
    homEquiv (DifferentialGradedBimodule.Derived.object N) M P f =
        TensorHom.derivedHomEquiv N M P
            ((Tensor.derivedBifunctorObjIso N).inv.app M ≫ f) ≫
          (InternalHom.derivedBifunctorObjIso N).inv.app P := sorry

/-- Uncurrying in the full parametrized adjunction computes by fixed-bimodule derived
uncurrying on a strict bimodule object. -/
@[simp, stacks 09LT "strict-object formula for parametrized derived uncurrying"]
theorem homEquiv_object_symm_apply
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : M ⟶ ((InternalHom.derivedBifunctor A B).obj
      (op (DifferentialGradedBimodule.Derived.object N))).obj P) :
    (homEquiv (DifferentialGradedBimodule.Derived.object N) M P).symm g =
      (Tensor.derivedBifunctorObjIso N).hom.app M ≫
        (TensorHom.derivedHomEquiv N M P).symm
          (g ≫ (InternalHom.derivedBifunctorObjIso N).hom.app P) := sorry

/-- Derived tensoring by an arbitrary derived bimodule is recognized as a left adjoint. -/
@[stacks 09LT "derived tensor by a derived bimodule is a left adjoint"]
noncomputable instance tensorObjIsLeftAdjoint
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B) :
    ((Tensor.derivedBifunctor A B).obj K).IsLeftAdjoint := sorry

/-- Derived internal Hom from an arbitrary derived bimodule is recognized as a right adjoint. -/
@[stacks 09LT "derived internal Hom from a derived bimodule is a right adjoint"]
noncomputable instance internalHomObjIsRightAdjoint
    (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B) :
    ((InternalHom.derivedBifunctor A B).obj (op K)).IsRightAdjoint := sorry

section AdjointInstances

variable (K : DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)

#synth ((Tensor.derivedBifunctor A B).obj K).IsLeftAdjoint
#synth ((InternalHom.derivedBifunctor A B).obj (op K)).IsRightAdjoint
#synth ((Tensor.derivedBifunctor A B).obj K).CommShift ℤ
#synth ((InternalHom.derivedBifunctor A B).obj (op K)).CommShift ℤ
#synth (adjunction K).CommShift ℤ
#synth ((Tensor.derivedBifunctor A B).obj K).IsTriangulated
#synth ((InternalHom.derivedBifunctor A B).obj (op K)).IsTriangulated
#synth (adjunction K).IsTriangulated

end AdjointInstances

end DifferentialGradedBimodule.TensorHom.Derived
