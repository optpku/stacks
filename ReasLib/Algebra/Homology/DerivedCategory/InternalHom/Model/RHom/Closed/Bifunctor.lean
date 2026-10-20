/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor.At
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison.Natural
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bifunctor comparison for canonical module RHom

Pointwise right-adjoint uniqueness compares `RHom_A(K, -)` with a selected internal-Hom functor
for each `K`, but does not by itself make those comparisons natural in `K`.  This leaf records the
exact coherent owner needed by two-variable constructions: a natural isomorphism of bifunctors.
It is intentionally separate from `RHom.ClosedComparison`, whose pointwise adjunction family is
enough for fixed-source calculations.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalClosed

namespace CategoryTheory.DerivedCategory.InternalHom.RHom

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- 0E1U: Same-universe compatibility name for the carrier-polymorphic coherent canonical module
`RHom` bifunctor comparison. -/
@[stacks 0E1U "same-universe bifunctor comparison for canonical module RHom"]
abbrev BifunctorComparison [RHom.Has (A := A)] :=
  RHom.At.BifunctorComparison (R := A)

/-- `0E1U:` A coherent ambient right-tensor adjunction for canonical same-universe module
`RHom`. -/
@[stacks 0E1U "same-universe parametrized tensor-RHom adjunction"]
abbrev TensorAdjunction₂ [RHom.Has (A := A)] :=
  MonoidalCategory.tensoringRight (DerivedCategory (ModuleCat.{u} A)) ⊣₂
    RHom.curried (A := A)

/-- `0E1U:` Canonical same-universe module `RHom` as a right internal-Hom owner. -/
@[stacks 0E1U "same-universe canonical RHom right internal-Hom owner"]
noncomputable abbrev rightInternalHomOf [RHom.Has (A := A)]
    (adj₂ : RHom.TensorAdjunction₂ (A := A)) :
    RightInternalHom (DerivedCategory (ModuleCat.{u} A)) :=
  RHom.At.rightInternalHomOf adj₂

/-- `0E1U:` The coherent same-universe bifunctor isomorphism produced by a parametrized
tensor-`RHom` adjunction. -/
@[stacks 0E1U "same-universe RHom bifunctor isomorphism from adjunction"]
noncomputable abbrev bifunctorIsoOfAdjunction [RHom.Has (A := A)]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (adj₂ : RHom.TensorAdjunction₂ (A := A)) :
    RHom.functor (A := A) ≅
      Functor.PullbackInternalHom.Bifunctor.internalHomFunctor H :=
  RHom.At.bifunctorIsoOfAdjunction H adj₂

namespace BifunctorComparison

variable [RHom.Has (A := A)]

/-- `0E1U:` Package an explicit coherent comparison between same-universe canonical `RHom` and a
selected internal-Hom bifunctor. -/
@[stacks 0E1U "construct same-universe RHom bifunctor comparison from explicit iso"]
noncomputable abbrev ofIso
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (e : RHom.functor (A := A) ≅
      Functor.PullbackInternalHom.Bifunctor.internalHomFunctor H) :
    RHom.BifunctorComparison (A := A) :=
  RHom.At.BifunctorComparison.ofIso H e

/-- `0E1U:` Construct the coherent same-universe comparison from a genuine parametrized
tensor-`RHom` adjunction. -/
@[stacks 0E1U "same-universe RHom comparison from parametrized adjunction"]
noncomputable abbrev ofAdjunction
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (adj₂ : RHom.TensorAdjunction₂ (A := A)) :
    RHom.BifunctorComparison (A := A) :=
  RHom.BifunctorComparison.ofIso H (RHom.bifunctorIsoOfAdjunction H adj₂)

/-- The selected closed structure carried by the carrier-polymorphic comparison. -/
@[stacks 0E1U "same-universe bifunctor comparison closed structure"]
abbrev closed (M : RHom.BifunctorComparison (A := A)) :
    MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) :=
  RHom.At.BifunctorComparison.closed M

/-- The coherent bifunctor isomorphism carried by the comparison. -/
@[stacks 0E1U "same-universe bifunctor comparison functor isomorphism"]
abbrev functorIso (M : RHom.BifunctorComparison (A := A)) :
    RHom.functor (A := A) ≅
      Functor.PullbackInternalHom.Bifunctor.internalHomFunctor M.closed :=
  RHom.At.BifunctorComparison.functorIso M

/-- 0E1U: The objectwise component of a coherent canonical-`RHom` comparison. -/
@[stacks 0E1U "bifunctor comparison object isomorphism"]
noncomputable abbrev objIso
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    RHom.obj (A := A) K L ≅ (ihomOf M.closed K).obj L :=
  RHom.At.BifunctorComparison.objIso M K L

/-- 0E1U: Contravariant source naturality of a coherent canonical-`RHom` comparison. -/
@[reassoc, stacks 0E1U "bifunctor comparison source naturality"]
theorem objIso_natural_source
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    RHom.map (A := A) f (𝟙 L) ≫ (M.objIso K₂ L).hom =
      (M.objIso K₁ L).hom ≫ (preOf M.closed f).app L :=
  RHom.At.BifunctorComparison.objIso_natural_source M f L

/-- 0E1U: Covariant target naturality of a coherent canonical-`RHom` comparison. -/
@[reassoc, stacks 0E1U "bifunctor comparison target naturality"]
theorem objIso_natural_target
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) :
    RHom.map (A := A) (𝟙 K) f ≫ (M.objIso K L₂).hom =
      (M.objIso K L₁).hom ≫ (ihomOf M.closed K).map f :=
  RHom.At.BifunctorComparison.objIso_natural_target M K f

/-- The same-universe fixed-target comparison is natural in the source variable. -/
@[reassoc, stacks 0E1U "same-universe fixed-target RHom naturality"]
theorem sourceIso_naturality
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    (RHom.At.sourceFunctor (R := A) L).map f.op ≫ (M.objIso K₂ L).hom =
      (M.objIso K₁ L).hom ≫
        ((MonoidalClosed.internalHomOf M.closed).flip.obj L).map f.op :=
  RHom.At.BifunctorComparison.sourceIso_naturality M f L

/-- The inverse same-universe fixed-target comparison is natural in the source variable. -/
@[reassoc, stacks 0E1U "inverse same-universe fixed-target RHom naturality"]
theorem sourceIso_inv_naturality
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    ((MonoidalClosed.internalHomOf M.closed).flip.obj L).map f.op ≫
        (M.objIso K₂ L).inv =
      (M.objIso K₁ L).inv ≫ (RHom.At.sourceFunctor (R := A) L).map f.op :=
  RHom.At.BifunctorComparison.sourceIso_inv_naturality M f L

/-- The same-universe fixed-target comparison assembled as a natural isomorphism. -/
noncomputable abbrev sourceIso
    (M : RHom.BifunctorComparison (A := A))
    (L : DerivedCategory (ModuleCat.{u} A)) :
    RHom.At.sourceFunctor (R := A) L ≅
      (MonoidalClosed.internalHomOf M.closed).flip.obj L :=
  RHom.At.BifunctorComparison.sourceIso M L

/-- The forward fixed-target component is the objectwise comparison. -/
@[simp, stacks 0E1U "same-universe fixed-target comparison component"]
theorem sourceIso_hom_app
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (M.sourceIso L).hom.app (Opposite.op K) = (M.objIso K L).hom :=
  RHom.At.BifunctorComparison.sourceIso_hom_app M K L

/-- The inverse fixed-target component is the inverse objectwise comparison. -/
@[simp, stacks 0E1U "inverse same-universe fixed-target comparison component"]
theorem sourceIso_inv_app
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (M.sourceIso L).inv.app (Opposite.op K) = (M.objIso K L).inv :=
  RHom.At.BifunctorComparison.sourceIso_inv_app M K L

/-- The same-universe fixed-source comparison is natural in the target variable. -/
@[reassoc, stacks 0E1U "same-universe fixed-source RHom naturality"]
theorem targetIso_naturality
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) :
    (RHom.At.targetFunctor (R := A) K).map f ≫ (M.objIso K L₂).hom =
      (M.objIso K L₁).hom ≫ (MonoidalClosed.ihomOf M.closed K).map f :=
  RHom.At.BifunctorComparison.targetIso_naturality M K f

/-- The inverse same-universe fixed-source comparison is natural in the target variable. -/
@[reassoc, stacks 0E1U "inverse same-universe fixed-source RHom naturality"]
theorem targetIso_inv_naturality
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) :
    (MonoidalClosed.ihomOf M.closed K).map f ≫ (M.objIso K L₂).inv =
      (M.objIso K L₁).inv ≫ (RHom.At.targetFunctor (R := A) K).map f :=
  RHom.At.BifunctorComparison.targetIso_inv_naturality M K f

/-- The same-universe fixed-source comparison assembled as a natural isomorphism. -/
noncomputable abbrev targetIso
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    RHom.At.targetFunctor (R := A) K ≅ MonoidalClosed.ihomOf M.closed K :=
  RHom.At.BifunctorComparison.targetIso M K

/-- The forward fixed-source component is the objectwise comparison. -/
@[simp, stacks 0E1U "same-universe fixed-source comparison component"]
theorem targetIso_hom_app
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (M.targetIso K).hom.app L = (M.objIso K L).hom :=
  RHom.At.BifunctorComparison.targetIso_hom_app M K L

/-- The inverse fixed-source component is the inverse objectwise comparison. -/
@[simp, stacks 0E1U "inverse same-universe fixed-source comparison component"]
theorem targetIso_inv_app
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (M.targetIso K).inv.app L = (M.objIso K L).inv :=
  RHom.At.BifunctorComparison.targetIso_inv_app M K L

end BifunctorComparison

namespace ClosedComparison

variable [RHom.Has (A := A)]

/-- `0E1U:` Package a coherent comparison already carried by a bundled closed presentation. -/
@[stacks 0E1U "construct RHom bifunctor comparison from closed presentation"]
noncomputable abbrev toBifunctorComparison
    (M : RHom.ClosedComparison (A := A))
    (e : RHom.functor (A := A) ≅
      Functor.PullbackInternalHom.Bifunctor.internalHomFunctor M.closed) :
    RHom.BifunctorComparison (A := A) :=
  RHom.BifunctorComparison.ofIso M.closed e

end ClosedComparison

end CategoryTheory.DerivedCategory.InternalHom.RHom
