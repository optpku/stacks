/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.FiniteType

/-!
# Covering-local finite generation of graded module sheaves

Finite homogeneous families generate locally when each homogeneous section admits
coefficient expressions on a covering sieve. The local names are compatibility aliases for
the predicates in `FiniteType`, which already express covering-local generation.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedModuleSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddCommGroup ι]
variable {𝒜 : GradedAlgebraSheaf 𝒪 ι}

/-- A fixed finite homogeneous family generates locally on an object if every homogeneous
section over an object above it has coefficient expressions after passing to a covering sieve.
The family is fixed independently of the degree, section, and covering sieve. -/
abbrev LocallyHomogeneouslyGeneratesOn
    (ℱ : GradedModuleSheaf 𝒜) (U : C) (r : ℕ)
    (degree : Fin r → ι)
    (generator : ∀ index : Fin r, (ℱ.obj (degree index)).val.obj (Opposite.op U)) : Prop :=
  HomogeneouslyGeneratesOn ℱ U r degree generator

/-- Covering-local homogeneous generation is the finite-type owner's generation predicate. -/
theorem locallyHomogeneouslyGeneratesOn_iff_homogeneouslyGeneratesOn
    (ℱ : GradedModuleSheaf 𝒜) (U : C) (r : ℕ)
    (degree : Fin r → ι)
    (generator : ∀ index : Fin r, (ℱ.obj (degree index)).val.obj (Opposite.op U)) :
    LocallyHomogeneouslyGeneratesOn ℱ U r degree generator ↔
      HomogeneouslyGeneratesOn ℱ U r degree generator := Iff.rfl

/-- The covering-local section criterion for a fixed finite homogeneous generating family. -/
theorem locallyHomogeneouslyGeneratesOn_iff
    (ℱ : GradedModuleSheaf 𝒜) (U : C) (r : ℕ)
    (degree : Fin r → ι)
    (generator : ∀ index : Fin r, (ℱ.obj (degree index)).val.obj (Opposite.op U)) :
    LocallyHomogeneouslyGeneratesOn ℱ U r degree generator ↔
      ∀ ⦃V : C⦄ (inclusion : V ⟶ U) (n : ι) (localSection : (ℱ.obj n).val.obj (Opposite.op V)),
        ∃ (cover : Sieve V), cover ∈ J V ∧
          ∀ ⦃W : C⦄ (restriction : W ⟶ V), cover restriction →
            ∃ (coefficientDegree : Fin r → ι)
              (degree_eq : ∀ index : Fin r, degree index + coefficientDegree index = n)
              (coefficient : ∀ index : Fin r,
                (𝒜.obj (coefficientDegree index)).val.obj (Opposite.op W)),
              (((ℱ.obj n).val.map restriction.op).hom localSection) = ∑ index : Fin r,
                cast (congrArg (fun degree ↦ ((ℱ.obj degree).val.obj (Opposite.op W) : Type (max u v))) (degree_eq index))
                  (ℱ.smul (degree index) (coefficientDegree index) (Opposite.op W)
                    (((ℱ.obj (degree index)).val.map (restriction ≫ inclusion).op).hom
                      (generator index)) (coefficient index)) := by
  have restriction_comp (n : ι) {U V W : C} (i : V ⟶ U) (f : W ⟶ V)
      (x : (ℱ.obj n).val.obj (Opposite.op U)) :
      (((ℱ.obj n).val.map (f ≫ i).op).hom x) =
        (((ℱ.obj n).val.map f.op).hom (((ℱ.obj n).val.map i.op).hom x)) := by
    change (ℱ.obj n).val.map (f ≫ i).op x =
      (ℱ.obj n).val.map f.op ((ℱ.obj n).val.map i.op x)
    rw [op_comp, PresheafOfModules.map_comp_apply]
  simp only [LocallyHomogeneouslyGeneratesOn, HomogeneouslyGeneratesOn, restriction_comp]

/-- A graded module sheaf is locally of finite type if a cover carries finite homogeneous
families that generate locally, using one family for all degrees on each cover member. -/
abbrev IsLocallyFiniteType (ℱ : GradedModuleSheaf 𝒜) : Prop :=
  IsFiniteType ℱ

/-- The local and finite-type interfaces use the same predicate on the same graded sheaf. -/
theorem isLocallyFiniteType_iff_isFiniteType (ℱ : GradedModuleSheaf 𝒜) :
    IsLocallyFiniteType ℱ ↔ IsFiniteType ℱ := Iff.rfl

/-- Local finite type is finite homogeneous generation on a cover, with expressions local
on each member rather than required on entire subobjects. -/
theorem isLocallyFiniteType_iff (ℱ : GradedModuleSheaf 𝒜) :
    IsLocallyFiniteType ℱ ↔
      ∃ (Index : Type u) (U : Index → C), J.CoversTop U ∧
        ∀ index : Index, ∃ (r : ℕ) (degree : Fin r → ι)
          (generator : ∀ generatorIndex : Fin r,
            (ℱ.obj (degree generatorIndex)).val.obj (Opposite.op (U index))),
          LocallyHomogeneouslyGeneratesOn ℱ (U index) r degree generator := Iff.rfl

end SheafOfModules.RingedSite.GradedModuleSheaf

