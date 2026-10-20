/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Distributive.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Alternating
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor description of the extended alternating Cech complex

The module-valued extended alternating Cech complex is obtained by tensoring the ring-valued
complex with the module.  This file owns the explicit localization-product, Cech-conerve, and
degreewise comparisons used in that isomorphism.

@stack 0G6H
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits ComplexShape ModuleCat MonoidalCategory
open AlgebraicTopology LocalizedModule
open scoped TensorProduct

namespace LocalizedModule.Away.Cech.Alternating.Tensor

variable {R : Type u} [CommRing R]
variable {r : ℕ}
variable (f : Fin r → R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Termwise tensoring by `M` on cochain complexes. -/
@[stacks 0G6H "termwise tensor functor for Cech complexes"]
abbrev complexFunctor :
    CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat R) ℕ :=
  (tensorLeft (of R M)).mapHomologicalComplex (up ℕ)

/-- The ring-valued principal-localization family arrow. -/
@[stacks 0G6H "ring-valued principal-localization family arrow"]
abbrev ringArrow : Arrow (ModuleCat R) :=
  Arrow.mk (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap R f))

/-- The module-valued principal-localization family arrow. -/
@[stacks 0G6H "module-valued principal-localization family arrow"]
abbrev moduleArrow : Arrow (ModuleCat R) :=
  Arrow.mk (ofHom (LocalizedModule.Away.Cech.familyMap M f))

/-- The ring-valued localization-family arrow after tensoring by `M`. -/
@[stacks 0G6H "tensor of the ring-valued localization-family arrow"]
abbrev tensorRingArrow : Arrow (ModuleCat R) :=
  (tensorLeft (of R M)).mapArrow.obj (ringArrow f)

/-- Termwise tensoring by `M` on cosimplicial modules. -/
@[stacks 0G6H "termwise tensor functor for cosimplicial modules"]
abbrev cosimplicialFunctor :
    CosimplicialObject (ModuleCat R) ⥤ CosimplicialObject (ModuleCat R) :=
  (CosimplicialObject.whiskering (ModuleCat R) (ModuleCat R)).obj (tensorLeft (of R M))

/-- Tensoring `M` with the product of the ring localizations is explicitly equivalent to the
product of the localized modules. -/
@[stacks 0G6H "tensor comparison for a principal-localization product"]
noncomputable def codomainLinearEquiv :
    M ⊗[R] (∀ i : Fin r, Localization.Away (f i)) ≃ₗ[R]
      ∀ i : Fin r, LocalizedModule.Away (f i) M :=
  (TensorProduct.piRight R R M (fun i : Fin r ↦ Localization.Away (f i))) ≪≫ₗ
    LinearEquiv.piCongrRight fun i : Fin r ↦
      TensorProduct.comm R M (Localization.Away (f i)) ≪≫ₗ
        (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M).symm.restrictScalars R

/-- The unit comparison and localization-product equivalence form the comparison square between
the tensorized ring arrow and the module arrow. -/
theorem familyMap_commSq :
    CommSq ((ρ_ (of R M)).symm).hom (moduleArrow f M).hom
      ((tensorLeft (of R M)).map (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap R f)))
      (codomainLinearEquiv f M).toModuleIso.inv := sorry

/-- The module localization-family arrow is explicitly isomorphic to the tensorized ring arrow. -/
@[stacks 0G6H "tensor comparison of localization-family arrows"]
noncomputable def arrowIso :
    moduleArrow f M ≅ (tensorLeft (of R M)).mapArrow.obj (ringArrow f) :=
  Arrow.isoMk ((ρ_ (of R M)).symm) ((codomainLinearEquiv f M).toModuleIso.symm)
    (familyMap_commSq f M).w

/-- At each simplex, tensoring commutes with the wide pushout defining the Cech conerve. -/
@[stacks 0G6H "simplexwise tensor comparison for the Cech conerve"]
noncomputable def conerveComponent (n : SimplexCategory) :
    (((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve).obj n ≅
      ((cosimplicialFunctor M).obj ((ringArrow f).cechConerve)).obj n :=
  (HasColimit.isoOfNatIso
      (WidePushoutShape.diagramIsoWideSpan
        ((WidePushoutShape.wideSpan (ringArrow f).left
          (fun _ : Fin (n.len + 1) ↦ (ringArrow f).right)
          fun _ ↦ (ringArrow f).hom) ⋙ tensorLeft (of R M)))).symm ≪≫
    (preservesColimitIso (tensorLeft (of R M))
      (WidePushoutShape.wideSpan (ringArrow f).left
        (fun _ : Fin (n.len + 1) ↦ (ringArrow f).right)
        fun _ ↦ (ringArrow f).hom)).symm

/-- The simplexwise tensor/Cech comparison is natural. -/
theorem conerveComponent_naturality {n n' : SimplexCategory} (α : n ⟶ n') :
    (((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve).map α ≫
        (conerveComponent f M n').hom =
      (conerveComponent f M n).hom ≫
        ((cosimplicialFunctor M).obj ((ringArrow f).cechConerve)).map α := sorry

/-- Tensoring the Cech conerve is naturally isomorphic to the Cech conerve of the tensorized
arrow. -/
@[stacks 0G6H "tensor comparison for the Cech conerve"]
noncomputable def conerveIso :
    ((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve ≅
      (cosimplicialFunctor M).obj ((ringArrow f).cechConerve) :=
  NatIso.ofComponents (conerveComponent f M)
    (fun α ↦ conerveComponent_naturality (f := f) (M := M) α)

/-- The module-valued Cech conerve is explicitly isomorphic to the tensorized ring-valued Cech
conerve. -/
@[stacks 0G6H "module-valued Cech conerve tensor comparison"]
noncomputable def moduleConerveIso :
    (moduleArrow f M).cechConerve ≅
      (cosimplicialFunctor M).obj ((ringArrow f).cechConerve) :=
  (CategoryTheory.CosimplicialObject.cechConerve :
    Arrow (ModuleCat.{u} R) ⥤ CosimplicialObject (ModuleCat.{u} R)).mapIso (arrowIso f M) ≪≫
    conerveIso f M

/-- Tensoring commutes with the alternating-coface complex functor. -/
theorem alternatingCofaceMapComplex_comp :
    alternatingCofaceMapComplex (ModuleCat R) ⋙ complexFunctor M =
      cosimplicialFunctor M ⋙ alternatingCofaceMapComplex (ModuleCat R) := sorry

/-- The ordinary module-valued alternating Cech complex is explicitly isomorphic to the
tensorized ring-valued complex. -/
@[stacks 0G6H "tensor comparison for the alternating Cech complex"]
noncomputable def complexIso :
    Alternating.complex f M ≅ (complexFunctor M).obj (Alternating.complex f R) :=
  (alternatingCofaceMapComplex (ModuleCat R)).mapIso (moduleConerveIso f M) ≪≫
    (eqToIso
      (Functor.congr_obj (alternatingCofaceMapComplex_comp (R := R) M)
        (ringArrow f).cechConerve)).symm

/-- Degree zero of the extended module-valued complex is its coefficient module. -/
theorem extended_X_zero_source :
    (Alternating.extended f M).X 0 = ModuleCat.of R M := sorry

/-- Degree zero of the tensorized ring-valued extended complex is `M ⊗[R] R`. -/
theorem extended_X_zero_target :
    ((complexFunctor M).obj (Alternating.extended f R)).X 0 =
      (tensorLeft (of R M)).obj (ModuleCat.of R R) := sorry

/-- Positive degree `n + 1` of the extended module-valued complex is degree `n` of the ordinary
complex. -/
theorem extended_X_succ_source (n : ℕ) :
    (Alternating.extended f M).X (n + 1) = (Alternating.complex f M).X n := sorry

/-- Positive degree `n + 1` of the tensorized ring-valued extended complex is degree `n` of the
tensorized ordinary complex. -/
theorem extended_X_succ_target (n : ℕ) :
    ((complexFunctor M).obj (Alternating.extended f R)).X (n + 1) =
      ((complexFunctor M).obj (Alternating.complex f R)).X n := sorry

/-- The explicit degreewise comparison between the module-valued extended Cech complex and the
tensorized ring-valued extended Cech complex. -/
@[stacks 0G6H "degreewise tensor comparison for the extended Cech complex"]
noncomputable def extendedComponentIso (i : ℕ) :
    (Alternating.extended f M).X i ≅
      ((complexFunctor M).obj (Alternating.extended f R)).X i :=
  match i with
  | 0 =>
      eqToIso (extended_X_zero_source f M) ≪≫ (ρ_ (of R M)).symm ≪≫
        eqToIso (extended_X_zero_target f M).symm
  | n + 1 =>
      eqToIso (extended_X_succ_source f M n) ≪≫
        (HomologicalComplex.eval (ModuleCat R) (up ℕ) n).mapIso (complexIso f M) ≪≫
        eqToIso (extended_X_succ_target f M n).symm

/-- The degreewise extended-Cech comparisons commute with the differentials. -/
theorem extendedComponentIso_comm
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (extendedComponentIso f M i).hom ≫
        ((complexFunctor M).obj (Alternating.extended f R)).d i j =
      (Alternating.extended f M).d i j ≫ (extendedComponentIso f M j).hom := sorry

/-- Lemma 15.29.2: the extended alternating Cech complex of `M` is canonically isomorphic to
the result of tensoring the ring-valued extended complex by `M`. -/
@[stacks 0G6H "Lemma 15.29.2"]
noncomputable def extendedIso :
    Alternating.extended f M ≅ (complexFunctor M).obj (Alternating.extended f R) :=
  HomologicalComplex.Hom.isoOfComponents (extendedComponentIso f M)
    (extendedComponentIso_comm f M)

end LocalizedModule.Away.Cech.Alternating.Tensor
