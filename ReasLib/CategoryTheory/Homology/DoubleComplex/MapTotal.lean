/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Functor
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Total.FiniteSupport
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Functors and Total Complexes

This file constructs the canonical comparison from the total complex obtained after applying an
additive functor termwise to the result of applying the functor to the original total complex.
For double complexes with finite support on each total-degree fibre, this comparison is an
isomorphism.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂ w₁ w₂ w₁₂

namespace HomologicalComplex₂

namespace Total.Map.Comparison

section Comparison

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (K : HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
variable [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂] [K.HasTotal c₁₂]
variable [((F.mapHomologicalComplex₂ c₁ c₂).obj K).HasTotal c₁₂]

/-- The degreewise comparison from the total of a termwise mapped double complex to the
termwise image of the original total complex. -/
@[stacks 0132 "additive-functor total comparison component"]
noncomputable def component (n : I₁₂) :
    (((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂).X n ⟶
      ((F.mapHomologicalComplex c₁₂).obj (K.total c₁₂)).X n :=
  ((F.mapHomologicalComplex₂ c₁ c₂).obj K).totalDesc
    (fun i₁ i₂ h ↦ F.map (K.ιTotal c₁₂ i₁ i₂ n h))

/-- On each mapped bidegree, `component` is the functorial image of the
corresponding inclusion into the original total complex. -/
@[reassoc (attr := simp)]
theorem ι_component
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotal c₁₂ i₁ i₂ n h ≫
        component F K c₁₂ n =
      F.map (K.ιTotal c₁₂ i₁ i₂ n h) := sorry

/-- The degreewise additive-functor/total comparison commutes with the total differentials. -/
theorem component_comm
    (n n' : I₁₂) (hnn' : c₁₂.Rel n n') :
    component F K c₁₂ n ≫
        ((F.mapHomologicalComplex c₁₂).obj (K.total c₁₂)).d n n' =
      (((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂).d n n' ≫
        component F K c₁₂ n' := sorry

/-- The canonical comparison from totalizing after applying an additive functor termwise to
applying the functor termwise after totalization. -/
@[stacks 0132 "additive-functor total comparison"]
noncomputable def hom :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂ ⟶
      (F.mapHomologicalComplex c₁₂).obj (K.total c₁₂) where
  f := component F K c₁₂
  comm' := component_comm F K c₁₂

/-- The components of `hom` are the canonical degreewise comparisons. -/
@[simp]
theorem hom_f (n : I₁₂) :
    (hom F K c₁₂).f n = component F K c₁₂ n := sorry

/-- The total comparison restricts on each bidegree to the functorial image of the original
total-complex inclusion. -/
@[reassoc (attr := simp)]
theorem ι_hom
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotal c₁₂ i₁ i₂ n h ≫
        (hom F K c₁₂).f n =
      F.map (K.ιTotal c₁₂ i₁ i₂ n h) := sorry

/-- The canonical projection from a total degree onto a bidegree summand. -/
noncomputable def projection (n : I₁₂) (i₁ : I₁) (i₂ : I₂) :
    (K.total c₁₂).X n ⟶ (K.X i₁).X i₂ := by
  classical
  exact K.totalDesc (fun j₁ j₂ _ ↦
    if h : (j₁, j₂) = (i₁, i₂) then
      eqToHom (congrArg (fun ij : I₁ × I₂ ↦ (K.X ij.1).X ij.2) h)
    else 0)

/-- A total projection is the identity on its own summand. -/
@[reassoc (attr := simp)]
theorem ι_projection
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    K.ιTotal c₁₂ i₁ i₂ n h ≫ projection K c₁₂ n i₁ i₂ = 𝟙 _ := by
  classical
  simp [projection]

/-- A total projection vanishes on every other summand. -/
@[reassoc (attr := simp)]
theorem ι_projection_ne
    (i₁ : I₁) (i₂ : I₂) (j₁ : I₁) (j₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (j₁, j₂) = n)
    (hne : (j₁, j₂) ≠ (i₁, i₂)) :
    K.ιTotal c₁₂ j₁ j₂ n h ≫ projection K c₁₂ n i₁ i₂ = 0 := by
  classical
  simp only [projection, ι_totalDesc, dif_neg hne]

end Comparison

section Naturality

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable {K L : HomologicalComplex₂ C c₁ c₂}
variable (c₁₂ : ComplexShape I₁₂)
variable [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
variable [K.HasTotal c₁₂] [L.HasTotal c₁₂]
variable [((F.mapHomologicalComplex₂ c₁ c₂).obj K).HasTotal c₁₂]
variable [((F.mapHomologicalComplex₂ c₁ c₂).obj L).HasTotal c₁₂]

/-- The additive-functor/total comparison is natural in the double complex. -/
@[reassoc]
theorem naturality (f : K ⟶ L) :
    HomologicalComplex₂.total.map ((F.mapHomologicalComplex₂ c₁ c₂).map f) c₁₂ ≫
        hom F L c₁₂ =
      hom F K c₁₂ ≫
        (F.mapHomologicalComplex c₁₂).map (HomologicalComplex₂.total.map f c₁₂) := sorry

end Naturality

section FiniteSupport

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (K : HomologicalComplex₂ C c₁ c₂) {c₁₂ : ComplexShape I₁₂}
variable [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂] [K.HasTotal c₁₂]
variable [((F.mapHomologicalComplex₂ c₁ c₂).obj K).HasTotal c₁₂]

/-- The reverse degreewise comparison is the finite sum of the mapped projections followed by
the corresponding inclusions. This is the explicit finite biproduct comparison formula. -/
noncomputable def invComponent (hfin : Total.Support.Finite (c := c₁₂) K) (n : I₁₂) :
    ((F.mapHomologicalComplex c₁₂).obj (K.total c₁₂)).X n ⟶
      (((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂).X n :=
  ∑ ij ∈ (hfin n).toFinset,
    F.map (projection K c₁₂ n ij.1 ij.2) ≫
      ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotalOrZero c₁₂ ij.1 ij.2 n

set_option backward.isDefEq.respectTransparency false in
/-- On a mapped bidegree inclusion, the reverse comparison is the corresponding inclusion into
the total of the mapped double complex. -/
@[reassoc (attr := simp)]
theorem map_ι_invComponent
    (hfin : Total.Support.Finite (c := c₁₂) K)
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    F.map (K.ιTotal c₁₂ i₁ i₂ n h) ≫ invComponent F K hfin n =
      ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotal c₁₂ i₁ i₂ n h := by
  classical
  dsimp only [Total.Support.Finite] at hfin
  by_cases hz : IsZero ((K.X i₁).X i₂)
  · exact (F.map_isZero hz).eq_of_src _ _
  · rw [invComponent, Preadditive.comp_sum, Finset.sum_eq_single (i₁, i₂)]
    · rw [← Category.assoc, ← F.map_comp, ι_projection, F.map_id, Category.id_comp,
        HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h]
    · intro ij _ hne
      rw [← Category.assoc, ← F.map_comp,
        ι_projection_ne K c₁₂ ij.1 ij.2 i₁ i₂ n h (Ne.symm hne), F.map_zero, zero_comp]
    · intro hnot
      exact (hnot ((hfin n).mem_toFinset.mpr ⟨h, hz⟩)).elim

/-- The reverse degreewise comparison commutes with the total differentials. -/
theorem invComponent_comm
    (hfin : Total.Support.Finite (c := c₁₂) K)
    (n n' : I₁₂) (hnn' : c₁₂.Rel n n') :
    invComponent F K hfin n ≫
        (((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂).d n n' =
      ((F.mapHomologicalComplex c₁₂).obj (K.total c₁₂)).d n n' ≫
        invComponent F K hfin n' := sorry

/-- The reverse total comparison assembled from its explicit finite-sum components. -/
noncomputable def inv (hfin : Total.Support.Finite (c := c₁₂) K) :
    (F.mapHomologicalComplex c₁₂).obj (K.total c₁₂) ⟶
      ((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂ where
  f := invComponent F K hfin
  comm' := invComponent_comm F K hfin

/-- The reverse total comparison has the specified finite-sum components. -/
@[simp]
theorem inv_f (hfin : Total.Support.Finite (c := c₁₂) K) (n : I₁₂) :
    (inv F K hfin).f n = invComponent F K hfin n := rfl

/-- An additive functor commutes canonically with a total complex having finite support on each
total-degree fibre. -/
@[stacks 0132 "additive functors commute with finite fibre-support totals"]
noncomputable def iso (hfin : Total.Support.Finite (c := c₁₂) K) :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂ ≅
      (F.mapHomologicalComplex c₁₂).obj (K.total c₁₂) where
  hom := hom F K c₁₂
  inv := inv F K hfin
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- For finite support on each total-degree fibre, the canonical comparison between applying an
additive functor before and after totalization is invertible. -/
@[stacks 0132 "additive functor total comparison for finite fibre support"]
theorem isIso (hfin : Total.Support.Finite (c := c₁₂) K) :
    IsIso (hom F K c₁₂) :=
  (iso F K hfin).isIso_hom

/-- The inverse map of `iso` is the comparison constructed from the finite-sum formula. -/
@[simp]
theorem iso_inv (hfin : Total.Support.Finite (c := c₁₂) K) :
    (iso F K hfin).inv = inv F K hfin := rfl

/-- The forward map of `iso` is the canonical total comparison. -/
@[simp]
theorem iso_hom (hfin : Total.Support.Finite (c := c₁₂) K) :
    (iso F K hfin).hom = hom F K c₁₂ := sorry

/-- The forward total-comparison isomorphism restricts on each bidegree to the image under `F`
of the original total-complex inclusion. -/
@[reassoc (attr := simp)]
theorem ι_iso_hom
    (hfin : Total.Support.Finite (c := c₁₂) K)
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotal c₁₂ i₁ i₂ n h ≫
        (iso F K hfin).hom.f n =
      F.map (K.ιTotal c₁₂ i₁ i₂ n h) := sorry

/-- The inverse comparison sends the image of each original total inclusion to the inclusion
of the corresponding mapped bidegree. -/
@[reassoc (attr := simp)]
theorem map_ι_iso_inv
    (hfin : Total.Support.Finite (c := c₁₂) K)
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    F.map (K.ιTotal c₁₂ i₁ i₂ n h) ≫ (iso F K hfin).inv.f n =
      ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotal c₁₂ i₁ i₂ n h :=
  map_ι_invComponent F K hfin i₁ i₂ n h

end FiniteSupport

section IsoNaturality

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable {K L : HomologicalComplex₂ C c₁ c₂}
variable {c₁₂ : ComplexShape I₁₂}
variable [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
variable [K.HasTotal c₁₂] [L.HasTotal c₁₂]
variable [((F.mapHomologicalComplex₂ c₁ c₂).obj K).HasTotal c₁₂]
variable [((F.mapHomologicalComplex₂ c₁ c₂).obj L).HasTotal c₁₂]

/-- Inverse naturality of the additive-functor comparison for finite-support total complexes. -/
@[reassoc, stacks 0132 "inverse naturality of the additive-functor total comparison"]
theorem iso_inv_naturality (f : K ⟶ L)
    (hK : Total.Support.Finite (c := c₁₂) K)
    (hL : Total.Support.Finite (c := c₁₂) L) :
    (F.mapHomologicalComplex c₁₂).map (HomologicalComplex₂.total.map f c₁₂) ≫
        (iso F L hL).inv =
      (iso F K hK).inv ≫
        HomologicalComplex₂.total.map
          ((F.mapHomologicalComplex₂ c₁ c₂).map f) c₁₂ := sorry

/-- Conjugating the mapped-total morphism by the comparison isomorphisms recovers the
termwise-mapped total morphism. -/
@[reassoc, stacks 0132 "source-map computation for the additive-functor total comparison"]
theorem iso_source_map (f : K ⟶ L)
    (hK : Total.Support.Finite (c := c₁₂) K)
    (hL : Total.Support.Finite (c := c₁₂) L) :
    (iso F K hK).hom ≫
        (F.mapHomologicalComplex c₁₂).map (HomologicalComplex₂.total.map f c₁₂) ≫
          (iso F L hL).inv =
      HomologicalComplex₂.total.map
        ((F.mapHomologicalComplex₂ c₁ c₂).map f) c₁₂ := sorry

/-- Conjugating the termwise-mapped total morphism by the inverse comparison recovers the
functorial image of the original total morphism. -/
@[reassoc, stacks 0132 "target-map computation for the additive-functor total comparison"]
theorem iso_target_map (f : K ⟶ L)
    (hK : Total.Support.Finite (c := c₁₂) K)
    (hL : Total.Support.Finite (c := c₁₂) L) :
    (iso F K hK).inv ≫
        HomologicalComplex₂.total.map
            ((F.mapHomologicalComplex₂ c₁ c₂).map f) c₁₂ ≫
          (iso F L hL).hom =
      (F.mapHomologicalComplex c₁₂).map
        (HomologicalComplex₂.total.map f c₁₂) := sorry

end IsoNaturality

end Total.Map.Comparison

end HomologicalComplex₂
