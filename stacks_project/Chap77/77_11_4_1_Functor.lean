/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap77.Lemma_77_11_2_InDimensions
public import stacks_project.Chap77.«77_7_1_1_BaseChange»
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions

/-!
# The flat-in-dimensions functor on algebraic spaces

Typed checks of the canonical functor and its flatness specifications, retaining
the import surface used by existing consumers.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsGE_pullback f ℱ n :
  ∀ {T T' : SchemeOver Y} (g : T' ⟶ T),
    Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n →
    Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T'.hom ℱ) (pullback.snd f T'.hom) n)

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsSubfunctor f ℱ n :
  CategoryTheory.Subfunctor ((Functor.const (SchemeOver Y)ᵒᵖ).obj (PUnit : Type u)))

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.mem_flatInDimensionsSubfunctor f ℱ n :
  ∀ T : SchemeOver Y,
    PUnit.unit ∈ (Flattening.flatInDimensionsSubfunctor f ℱ n).obj (op T) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n)

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor f ℱ n :
  (SchemeOver Y)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor_nonempty_iff f ℱ n :
  ∀ T : SchemeOver Y,
    Nonempty ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n)

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor_isEmpty_iff f ℱ n :
  ∀ T : SchemeOver Y,
    IsEmpty ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      ¬ Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n)

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctorObjSubsingleton f ℱ n :
  ∀ T : SchemeOver Y, Subsingleton ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op T)))

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor_nonempty_iff_mk f ℱ n :
  ∀ {T : Over S} (a : ofOver T ⟶ Y),
    Nonempty ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op (SchemeOver.mk a))) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f a ℱ) (pullback.snd f a) n)

#check (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor_isEmpty_iff_mk f ℱ n :
  ∀ {T : Over S} (a : ofOver T ⟶ Y),
    IsEmpty ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op (SchemeOver.mk a))) ↔
      ¬ Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f a ℱ) (pullback.snd f a) n)
