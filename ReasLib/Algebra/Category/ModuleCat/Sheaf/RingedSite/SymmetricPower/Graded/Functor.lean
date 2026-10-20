/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Graded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of the graded symmetric algebra

This leaf upgrades degreewise symmetric-power maps to homomorphisms of graded algebra sheaves and
packages the construction as a functor. Consumers needing only the graded object or its
commutativity can import the narrower `SymmetricPower.Graded` owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- A symmetric-power sheaf map preserves the canonical degree-zero section. -/
theorem map_oneSection
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (U : Cᵒᵖ) :
    (((map 𝒪 f 0).val.app U).hom) (oneSection 𝒪 F U) = oneSection 𝒪 G U := sorry

/-- A symmetric-power sheaf map preserves multiplication of homogeneous local sections. -/
theorem map_mulSection
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G)
    (U : Cᵒᵖ) (n m : ℕ) (a : (sheaf 𝒪 F n).val.obj U)
    (b : (sheaf 𝒪 F m).val.obj U) :
    (((map 𝒪 f (n + m)).val.app U).hom) (mulSection 𝒪 F U n m a b) =
      mulSection 𝒪 G U n m
        ((((map 𝒪 f n).val.app U).hom) a)
        ((((map 𝒪 f m).val.app U).hom) b) := sorry

/-- A module-sheaf morphism induces a homomorphism of graded symmetric algebra sheaves. -/
@[stacks 01CF "functoriality of the graded symmetric algebra"]
noncomputable def gradedMap
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    graded 𝒪 F ⟶ graded 𝒪 G where
  hom n := map 𝒪 f n
  map_one := map_oneSection 𝒪 f
  map_mul := map_mulSection 𝒪 f

/-- The graded symmetric algebra carries identity morphisms to identity homomorphisms. -/
theorem gradedMap_id (F : ringedSiteModuleCategory J 𝒪) :
    gradedMap 𝒪 (𝟙 F) = 𝟙 (graded 𝒪 F) := sorry

/-- The graded symmetric algebra carries composites to composites. -/
theorem gradedMap_comp
    {F G H : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (g : G ⟶ H) :
    gradedMap 𝒪 (f ≫ g) = gradedMap 𝒪 f ≫ gradedMap 𝒪 g := sorry

/-- The graded symmetric algebra functor on module sheaves over a commutative ringed site. -/
@[stacks 01CF "graded symmetric algebra functor"]
noncomputable def gradedFunctor :
    ringedSiteModuleCategory J 𝒪 ⥤ GradedAlgebraSheaf 𝒪 ℕ where
  obj := graded 𝒪
  map := gradedMap 𝒪
  map_id := gradedMap_id 𝒪
  map_comp := gradedMap_comp 𝒪

end SheafOfModules.RingedSite.SymmetricPower
