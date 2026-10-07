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

/-- For finite support on each total-degree fibre, the canonical comparison between applying an
additive functor before and after totalization is invertible. -/
@[stacks 0132 "additive functor total comparison for finite fibre support"]
theorem isIso (hfin : Total.Support.Finite (c := c₁₂) K) :
    IsIso (hom F K c₁₂) := sorry

/-- An additive functor commutes canonically with a total complex having finite support on each
total-degree fibre. -/
@[stacks 0132 "additive functors commute with finite fibre-support totals"]
noncomputable def iso (hfin : Total.Support.Finite (c := c₁₂) K) :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c₁₂ ≅
      (F.mapHomologicalComplex c₁₂).obj (K.total c₁₂) :=
  @asIso _ _ _ _ (hom F K c₁₂) (isIso F K hfin)

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
