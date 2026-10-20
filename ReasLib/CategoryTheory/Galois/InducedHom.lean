/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Galois.Action
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

universe u v u' v' w

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
variable {C' : Type u'} [Category.{v'} C'] [GaloisCategory C']
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
variable (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']

/-- The monoid homomorphism obtained by whiskering an automorphism of `F'` along `H`
and conjugating by a fibre isomorphism `t : H ⋙ F' ≅ F`. -/
def inducedMonoidHom (H : C ⥤ C') (t : H ⋙ F' ≅ F) : Aut F' →* Aut F :=
  MonoidHom.comp t.conjAut.toMonoidHom (((whiskeringLeft C C' FintypeCat).obj H).mapAut F')

/-- The continuous homomorphism determined by a fibre isomorphism
`t : H ⋙ F' ≅ F`. -/
def inducedContinuousHomCore (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    ContinuousMonoidHom (Aut F') (Aut F) where
  toMonoidHom := inducedMonoidHom F F' H t
  continuous_toFun := sorry

/-- Evaluation of the continuous homomorphism induced by a fibre isomorphism. -/
theorem inducedContinuousHom_apply (H : C ⥤ C') (t : H ⋙ F' ≅ F) (g : Aut F') :
    inducedContinuousHomCore F F' H t g =
      t.conjAut (((whiskeringLeft C C' FintypeCat).obj H).mapAut F' g) :=
  sorry

/-- The homomorphism induced by a fibre isomorphism gives a comparison square
between the finite continuous action realizations. -/
@[implicit_reducible]
def inducedContinuousHomCore_catCommSq (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    CatCommSq H (functorToContAction F) (functorToContAction F')
      (ContAction.res FintypeCat (inducedContinuousHomCore F F' H t)) where
  iso := NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (Action.mkIso (t.app X) fun _ ↦ sorry))
    (fun morphism ↦ ObjectProperty.hom_ext _
      (Action.hom_ext _ _ (t.hom.naturality morphism)))

/-- Changing the fibre isomorphism changes the induced homomorphism by an inner
automorphism of `Aut F`. -/
theorem inducedContinuousHomCore_conj (H : C ⥤ C') (t t' : H ⋙ F' ≅ F) :
    ∃ g : Aut F, ∀ σ : Aut F',
      inducedContinuousHomCore F F' H t' σ =
        g * inducedContinuousHomCore F F' H t σ * g⁻¹ :=
  sorry

end CategoryTheory.PreGaloisCategory
