/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite support on total-complex fibres

This leaf isolates the only support hypothesis needed to replace a coproduct indexed by a total
degree with a finite coproduct.  It is shape-polymorphic: the cohomological antidiagonal predicate
used by spectral sequences is a specialization in `DoubleComplex.TotalSupport`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe u v u' v' w₁ w₂ w

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c]

namespace Total.Support

/-- Every fibre of the total-degree map contains only finitely many nonzero bidegrees.

The predicate records pairs of indices rather than choosing a section of the total-degree map.
This makes it applicable to arbitrary complex shapes, including shapes where a total degree does
not determine one coordinate from the other.
-/
@[stacks 0132 "finite support on total-complex fibres"]
def Finite (K : HomologicalComplex₂ C c₁ c₂) : Prop :=
  ∀ n : I,
    {ij : I₁ × I₂ |
      ComplexShape.π c₁ c₂ c ij = n ∧ ¬ IsZero ((K.X ij.1).X ij.2)}.Finite

namespace Finite

variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- A zero-morphism-preserving functor transports finite total-degree support. -/
@[stacks 0132 "functoriality of finite total support"]
theorem map {K : HomologicalComplex₂ C c₁ c₂}
    (hfin : Total.Support.Finite (c := c) K)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    Total.Support.Finite (c := c)
      ((F.mapHomologicalComplex₂ c₁ c₂).obj K) := sorry

end Finite

section Totalization

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c]

/-- A total-degree coproduct with zero summands removed. Its injections are the finite
coproduct injections on the nonzero support and zero on every omitted summand. -/
noncomputable def Finite.coproductCocone [HasFiniteCoproducts C]
    {K : HomologicalComplex₂ C c₁ c₂}
    (hfin : Total.Support.Finite (c := c) K) (n : I) :
    ColimitCocone (Discrete.functor
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) n)) := by
  classical
  let S := {ij : I₁ × I₂ |
    ComplexShape.π c₁ c₂ c ij = n ∧ ¬ IsZero ((K.X ij.1).X ij.2)}
  letI := (hfin n).fintype
  let F : S → C := fun ij ↦ (K.X ij.1.1).X ij.1.2
  let t : K.toGradedObject.CofanMapObjFun (ComplexShape.π c₁ c₂ c) n :=
    GradedObject.CofanMapObjFun.mk _ _ _ (∐ F) (fun ij hi ↦
      if h : ¬ IsZero ((K.X ij.1).X ij.2) then Sigma.ι F ⟨ij, hi, h⟩ else 0)
  refine ⟨t, Cofan.IsColimit.mk _
    (fun s ↦ Sigma.desc (fun ij : S ↦ s.inj ⟨ij.1, ij.2.1⟩)) ?_ ?_⟩
  · intro s ij
    change (if h : ¬ IsZero ((K.X ij.1.1).X ij.1.2) then
      Sigma.ι F ⟨ij.1, ij.2, h⟩ else
      (0 : (K.X ij.1.1).X ij.1.2 ⟶ ∐ F)) ≫
        Sigma.desc (fun ij : S ↦ s.inj ⟨ij.1, ij.2.1⟩) = s.inj ij
    by_cases h : ¬ IsZero ((K.X ij.1.1).X ij.1.2)
    · rw [dif_pos h]
      exact Sigma.ι_desc (f := F) _ _
    · rw [dif_neg h]
      exact (not_not.mp h).eq_of_src _ _
  · intro s m hm
    change (m : (∐ F) ⟶ s.pt) = Sigma.desc (fun ij : S ↦ s.inj ⟨ij.1, ij.2.1⟩)
    apply Sigma.hom_ext (f := F)
    intro ij
    have h := hm ⟨ij.1, ij.2.1⟩
    change (if h : ¬ IsZero ((K.X ij.1.1).X ij.1.2) then
      Sigma.ι F ⟨ij.1, ij.2.1, h⟩ else
      (0 : (K.X ij.1.1).X ij.1.2 ⟶ ∐ F)) ≫ m = s.inj ⟨ij.1, ij.2.1⟩ at h
    erw [Sigma.ι_desc (f := F)]
    simpa only [dif_pos ij.2.2] using h

/-- Finite total-degree support is sufficient for totalization in a category with finite
coproducts. -/
@[stacks 0132 "finite support gives a total complex"]
theorem Finite.hasTotal [HasFiniteCoproducts C]
    {K : HomologicalComplex₂ C c₁ c₂}
    (hfin : Total.Support.Finite (c := c) K) :
    K.HasTotal c :=
  fun n ↦ ⟨⟨Finite.coproductCocone hfin n⟩⟩

end Totalization

namespace Finite

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c]

/-- A finite-support total has injective terms whenever all of its bidegree terms are injective.

This is the shape-polymorphic owner; cohomological double complexes use it through the
`AntidiagonalSupport.Finite` facade.
-/
@[stacks 0132 "injectivity of a finite-support total"]
theorem injective [DecidableEq I]
    {K : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c]
    (hfin : Total.Support.Finite (c := c) K)
    (hinj : ∀ i₁ i₂, Injective ((K.X i₁).X i₂)) (n : I) :
    Injective ((K.total c).X n) := by
  classical
  letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  letI := (hfin n).fintype
  let F : {ij : I₁ × I₂ |
      ComplexShape.π c₁ c₂ c ij = n ∧ ¬ IsZero ((K.X ij.1).X ij.2)} → C :=
    fun ij ↦ (K.X ij.1.1).X ij.1.2
  letI : ∀ ij, Injective (F ij) := fun ij ↦ hinj ij.1.1 ij.1.2
  have hF : Injective (∐ F) :=
    Injective.of_iso (biproduct.isoCoproduct F) inferInstance
  let cc := Finite.coproductCocone hfin n
  have hcc : Injective cc.cocone.pt := hF
  exact Injective.of_iso
    (IsColimit.coconePointUniqueUpToIso cc.isColimit
      (K.toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c) n)) hcc

end Finite

end Total.Support

end HomologicalComplex₂
