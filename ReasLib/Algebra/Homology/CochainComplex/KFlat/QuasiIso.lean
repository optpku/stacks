/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.QuasiIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-isomorphisms and K-flat tensor factors

@stack 06Y0
@stack 06YP
@stack 06YT

This file contains the two tensor invariance statements used by K-flat derived-functor
constructions.  The first fixes a K-flat right factor.  The second uses K-flat resolutions to
allow an arbitrary left factor while varying the right factor between K-flat complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v

namespace CochainComplex.IsKFlat

section FixedRight

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [CategoryWithHomology C] [MonoidalCategory C] [MonoidalPreadditive C]
variable {K : CochainComplex C ℤ}
variable [∀ X : CochainComplex C ℤ,
  CochainComplex.HasMapBifunctor X K (curriedTensor C)]

/-- Tensoring a quasi-isomorphism on the right by a fixed K-flat complex preserves
quasi-isomorphisms. -/
@[stacks 06Y0 "fixed K-flat tensor factor preserves quasi-isomorphisms",
  stacks 06YP "K-flat tensor invariance"]
theorem quasiIso_tensorHom_left {L M : CochainComplex C ℤ}
    (hK : K.IsKFlat) (f : L ⟶ M) [QuasiIso f] :
    QuasiIso (HomologicalComplex.tensorHom f (𝟙 K)) := sorry

end FixedRight

section VaryingRight

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ X Y : CochainComplex C ℤ,
  CochainComplex.HasMapBifunctor X Y (curriedTensor C)]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : C,
  PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X : C,
  PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
variable [HomotopyCategory.KFlat.HasResolutions C]

/-- If K-flat resolutions exist, tensoring an arbitrary complex with a quasi-isomorphism
between K-flat complexes preserves quasi-isomorphisms. -/
@[stacks 06YT "quasi-isomorphisms between K-flat complexes"]
theorem quasiIso_tensorHom_right
    (F : CochainComplex C ℤ) {P Q : CochainComplex C ℤ}
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) f) := sorry

end VaryingRight
end CochainComplex.IsKFlat
