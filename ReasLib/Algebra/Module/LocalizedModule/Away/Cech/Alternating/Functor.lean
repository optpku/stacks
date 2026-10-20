/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Tensor
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalSymmetry

/-!
# Functorial alternating Cech complexes

This module makes the alternating Cech complex of a finite family of principal
localizations functorial in its coefficient module and totalizes the resulting
bicomplex with the Cech degree first.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂ MonoidalCategory

noncomputable section

universe u

namespace LocalizedModule.Away.Cech.Alternating

variable {A : Type u} [CommRing A] {r : ℕ}

/-- A coefficient-module morphism induces a morphism of alternating Cech complexes. -/
noncomputable def complexMap (f : Fin r → A) {M N : ModuleCat.{u, u} A}
    (g : M ⟶ N) : complex f M ⟶ complex f N :=
  (Tensor.complexIso f M).hom ≫
    (NatTrans.mapHomologicalComplex
      ((curriedTensor (ModuleCat A)).map g) (up ℕ)).app (complex f A) ≫
    (Tensor.complexIso f N).inv

/-- The alternating-Cech morphism induced by an identity is the identity. -/
theorem complexMap_id (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    complexMap f (𝟙 M) = 𝟙 (complex f M) := sorry

/-- Alternating-Cech morphisms respect composition of coefficient morphisms. -/
theorem complexMap_comp (f : Fin r → A) {M N P : ModuleCat.{u, u} A}
    (g : M ⟶ N) (h : N ⟶ P) :
    complexMap f (g ≫ h) = complexMap f g ≫ complexMap f h := sorry

/-- The alternating Cech complex, functorial in its coefficient module. -/
noncomputable def complexFunctor (f : Fin r → A) :
    ModuleCat.{u, u} A ⥤ CochainComplex (ModuleCat.{u, u} A) ℕ where
  obj M := complex f M
  map g := complexMap f g
  map_id M := complexMap_id f M
  map_comp g h := complexMap_comp f g h

/-- Evaluating the alternating-Cech functor gives the alternating Cech complex. -/
theorem complexFunctor_obj (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    (complexFunctor f).obj M = complex f M := sorry

/-- The map of the alternating-Cech functor is the canonical coefficient map. -/
theorem complexFunctor_map (f : Fin r → A) {M N : ModuleCat.{u, u} A}
    (g : M ⟶ N) :
    (complexFunctor f).map g = complexMap f g := sorry

/-- The alternating-Cech functor preserves zero morphisms. -/
instance complexFunctor_preservesZeroMorphisms (f : Fin r → A) :
    (complexFunctor f).PreservesZeroMorphisms := sorry

/-- The alternating Cech complex extended by zero from natural to integer degrees. -/
abbrev row (f : Fin r → A) :
    ModuleCat.{u, u} A ⥤ CochainComplex (ModuleCat.{u, u} A) ℤ :=
  complexFunctor f ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u, u} A)

/-- The Cech-first total of the bicomplex obtained by applying the alternating-Cech row
termwise to a complex of coefficient modules. -/
noncomputable def total (f : Fin r → A) :
    CochainComplex (ModuleCat.{u, u} A) ℤ ⥤
      CochainComplex (ModuleCat.{u, u} A) ℤ :=
  (row f).mapHomologicalComplex (up ℤ) ⋙
    flipFunctor (ModuleCat.{u, u} A) (up ℤ) (up ℤ) ⋙
    totalFunctor (ModuleCat.{u, u} A) (up ℤ) (up ℤ) (up ℤ)

end LocalizedModule.Away.Cech.Alternating

end
