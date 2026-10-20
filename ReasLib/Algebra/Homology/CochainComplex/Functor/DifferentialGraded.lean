/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy

/-!
# Additive Functors as DG Functors of Cochain Complexes

An additive functor acts degreewise on the Hom complexes of cochain complexes.
This file packages that action as a differential graded functor and records
the concrete computation rules inherited by its closed and homotopy-category
companions.
-/

@[expose] public section

open CategoryTheory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

noncomputable section

universe u u' v v'

namespace CategoryTheory

variable {𝒝 : Type u} {𝒝' : Type u'}
variable [Category.{v} 𝒝] [Category.{v'} 𝒝']
variable [Preadditive 𝒝] [Preadditive 𝒝']
variable (F : 𝒝 ⥤ 𝒝') [F.Additive]

namespace Functor

/-- Lemma 22.26.7: an additive functor induces a differential graded functor on cochain
complexes.  Its object map is `F.mapHomologicalComplex (ComplexShape.up ℤ)`, and it maps a
homogeneous cochain using `Cochain.map`. -/
@[stacks 09LB]
def mapCochainDg :
    DgFunctor ℤ (CochainComplex 𝒝 ℤ) (CochainComplex 𝒝' ℤ) where
  obj := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
  map {A B} {n} f := Cochain.map f F
  map_add := sorry
  map_smul := sorry
  map_d := sorry
  map_id := sorry
  map_comp := sorry

namespace mapCochainDg

/-- The cochain-complex DG functor induced by `F` acts on objects by the usual functor on
complexes. -/
@[simp]
theorem obj (A : CochainComplex 𝒝 ℤ) :
    F.mapCochainDg.obj A =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A := sorry

/-- The cochain-complex DG functor induced by `F` acts on homogeneous cochains by
`Cochain.map`. -/
@[simp]
theorem map {A B : CochainComplex 𝒝 ℤ} {n : ℤ} (f : Cochain A B n) :
    F.mapCochainDg.map f = Cochain.map f F := sorry

namespace mapComp

/-- On the category of closed degree-zero cochains, the DG functor induced by `F` has the
expected object map. -/
@[simp]
theorem obj (A : CochainComplex 𝒝 ℤ) :
    F.mapCochainDg.mapComp.obj
        (⟨A⟩ : Comp ℤ (CochainComplex 𝒝 ℤ)) =
      (⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A⟩ :
        Comp ℤ (CochainComplex 𝒝' ℤ)) := sorry

/-- The underlying homogeneous cochain of the mapped closed cochain is obtained by applying
`Cochain.map` to its underlying cochain. -/
@[simp]
theorem hom_val {A B : CochainComplex 𝒝 ℤ} (f : CompHom A B) :
    (DgFunctor.mapCompHom F.mapCochainDg f).val = Cochain.map f.val F := sorry

/-- On closed degree-zero cochains, the induced functor acts through `mapCompHom`. -/
@[simp]
theorem map {A B : CochainComplex 𝒝 ℤ} (f : CompHom A B) :
    F.mapCochainDg.mapComp.map f =
      DgFunctor.mapCompHom F.mapCochainDg f := sorry

end mapComp

namespace mapK

/-- On the homotopy category of cochain complexes, the DG functor induced by `F` has the
expected object map. -/
@[simp]
theorem obj (A : CochainComplex 𝒝 ℤ) :
    F.mapCochainDg.mapK.obj
        (⟨A⟩ : K ℤ (CochainComplex 𝒝 ℤ)) =
      (⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A⟩ :
        K ℤ (CochainComplex 𝒝' ℤ)) := sorry

/-- The image of a represented cochain-complex homotopy class is represented by the mapped
closed cochain. -/
@[simp]
theorem map_toHomotopyClass {A B : CochainComplex 𝒝 ℤ} (f : CompHom A B) :
    F.mapCochainDg.mapK.map f.toHomotopyClass =
      (DgFunctor.mapCompHom F.mapCochainDg f).toHomotopyClass := sorry

/-- Passing to `K` after the closed-morphism functor agrees with the homotopy-category functor
induced by `F`. -/
@[simp]
theorem map_inK {A B : CochainComplex 𝒝 ℤ} (f : CompHom A B) :
    F.mapCochainDg.mapK.map f.inK =
      (F.mapCochainDg.mapComp.map f).inK := sorry

end mapK

end mapCochainDg

end Functor

end CategoryTheory
