/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit.Preserves
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely generated subalgebras of filtered colimits

This leaf records the finite-presentation consequence needed to descend a finitely generated
subalgebra of a filtered colimit of commutative algebras over an arbitrary commutative base ring
to one stage of the diagram.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CommAlgCat


/-- Finite-presentation core: a finitely presented subalgebra factors through one
stage of a filtered colimit. -/
theorem exists_fp_subalgebra_factorization
    {k : Type u} {I : Type v} [CommRing k] [SmallCategory I] [IsFiltered I]
    [UnivLE.{v, u}] (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k))
    [Algebra.FinitePresentation k T] :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i),
      (colimit.ι F i).hom.comp φ = T.val := sorry

/-- Finite-presentation core: the stage factorization can be chosen injective. -/
theorem exists_injective_stage_of_fp_subalgebra_colimit
    {k : Type u} {I : Type v} [CommRing k] [SmallCategory I] [IsFiltered I]
    [UnivLE.{v, u}] (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k))
    [Algebra.FinitePresentation k T] :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i), Function.Injective φ := sorry

section FieldCorollaries

variable {k : Type u} {I : Type v} [Field k] [SmallCategory I] [IsFiltered I]
  [UnivLE.{v, u}]

/-- A finitely generated subalgebra over a field factors through one filtered stage. -/
@[stacks 037N "filtered-colimit finite-stage factorization spec"]
theorem exists_fg_subalgebra_factorization
    (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k)) (hT : T.FG) :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i),
      (colimit.ι F i).hom.comp φ = T.val := sorry

/-- A finitely generated subalgebra over a field admits an injective map to one stage. -/
@[stacks 037N "filtered-colimit finite-stage factorization"]
theorem exists_injective_stage_of_fg_subalgebra_colimit
    (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k)) (hT : T.FG) :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i), Function.Injective φ := sorry

end FieldCorollaries

end CommAlgCat
