/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul.Monoid
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of Koszul algebras

A linear form on a module sheaf is an object over the structure module.  A morphism of linear
forms induces the exterior-power map in every degree; these maps assemble into a chain map and,
functorially, into a morphism of commutative Koszul algebras.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

-- Universe-bounded tensor-colimit preservation makes the induced structures larger.
set_option synthInstance.maxSize 1024

universe u v

namespace SheafOfModules.RingedSite.Koszul

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The category of module sheaves equipped with a linear form to the structure module. -/
@[stacks 062K "linear forms defining Koszul complexes"]
abbrev LinearForm := Over (unitModule J O)

/-- The chain map of Koszul complexes induced by a morphism of linear forms. -/
@[stacks 062K "functoriality map of Koszul complexes"]
noncomputable def map {phi psi : LinearForm O} (f : phi ⟶ psi) :
    complex O phi.hom ⟶ complex O psi.hom where
  f n := ExteriorPower.map O f.left n
  comm' := sorry

/-- In degree `n`, the Koszul chain map is the corresponding exterior-power map. -/
@[simp]
theorem map_f {phi psi : LinearForm O} (f : phi ⟶ psi) (n : ℕ) :
    (map O f).f n = ExteriorPower.map O f.left n := sorry

/-- Exterior-power maps commute with the Koszul differential in every degree. -/
@[stacks 062K "naturality of the Koszul differential", reassoc]
theorem map_differential {phi psi : LinearForm O} (f : phi ⟶ psi) (n : ℕ) :
    ExteriorPower.map O f.left (n + 1) ≫ differential O psi.hom n =
      differential O phi.hom n ≫ ExteriorPower.map O f.left n := sorry

/-- The Koszul chain map of an identity morphism is the identity. -/
theorem map_id (phi : LinearForm O) :
    map O (𝟙 phi) = 𝟙 (complex O phi.hom) := sorry

/-- Koszul chain maps preserve composition. -/
theorem map_comp {phi psi chi : LinearForm O} (f : phi ⟶ psi) (g : psi ⟶ chi) :
    map O (f ≫ g) = map O f ≫ map O g := sorry

/-- The Koszul chain-complex functor on module sheaves with a chosen linear form. -/
@[stacks 062K "Koszul chain-complex functor"]
noncomputable def complexFunctor :
    LinearForm O ⥤ ChainComplex (ringedSiteModuleCategory J O) ℕ where
  obj phi := complex O phi.hom
  map := map O
  map_id := map_id O
  map_comp := map_comp O

/-- The Koszul-complex functor sends a linear form to its Koszul complex. -/
@[simp]
theorem complexFunctor_obj (phi : LinearForm O) :
    (complexFunctor O).obj phi = complex O phi.hom := sorry

/-- On morphisms, the Koszul-complex functor is the degreewise exterior-power map. -/
@[simp]
theorem complexFunctor_map {phi psi : LinearForm O} (f : phi ⟶ psi) :
    (complexFunctor O).map f = map O f := sorry

/-- The Koszul chain map preserves the exterior unit. -/
theorem map_one {phi psi : LinearForm O} (f : phi ⟶ psi) :
    oneHom O phi.hom ≫ map O f = oneHom O psi.hom := sorry

/-- The Koszul chain map preserves exterior multiplication. -/
theorem map_mul {phi psi : LinearForm O} (f : phi ⟶ psi) :
    mulHom O phi.hom ≫ map O f =
      (map O f ⊗ₘ map O f) ≫ mulHom O psi.hom := sorry

/-- The commutative-monoid morphism of Koszul algebras induced by a morphism of linear forms. -/
@[stacks 062K "functoriality map of Koszul algebras"]
noncomputable def commMonMap {phi psi : LinearForm O} (f : phi ⟶ psi) :
    commMon O phi.hom ⟶ commMon O psi.hom :=
  CommMon.homMk (Mon.Hom.mk' (map O f) (map_one O f) (map_mul O f))

/-- Forgetting multiplication from a Koszul-algebra map recovers its Koszul chain map. -/
@[simp]
theorem commMonMap_hom {phi psi : LinearForm O} (f : phi ⟶ psi) :
    (commMonMap O f).hom.hom = map O f := sorry

/-- In degree `n`, a Koszul-algebra map is the corresponding exterior-power map. -/
@[simp]
theorem commMonMap_hom_f {phi psi : LinearForm O} (f : phi ⟶ psi) (n : ℕ) :
    (commMonMap O f).hom.hom.f n = ExteriorPower.map O f.left n := sorry

/-- The Koszul-algebra map of an identity morphism is the identity. -/
theorem commMonMap_id (phi : LinearForm O) :
    commMonMap O (𝟙 phi) = 𝟙 (commMon O phi.hom) := sorry

/-- Koszul-algebra maps preserve composition. -/
theorem commMonMap_comp {phi psi chi : LinearForm O}
    (f : phi ⟶ psi) (g : psi ⟶ chi) :
    commMonMap O (f ≫ g) = commMonMap O f ≫ commMonMap O g := sorry

/-- The functor assigning its commutative Koszul algebra to a module sheaf with a linear form. -/
@[stacks 062K "commutative Koszul-algebra functor"]
noncomputable def commMonFunctor :
    LinearForm O ⥤ CommMon (ChainComplex (ringedSiteModuleCategory J O) ℕ) where
  obj phi := commMon O phi.hom
  map := commMonMap O
  map_id := commMonMap_id O
  map_comp := commMonMap_comp O

/-- The commutative Koszul-algebra functor sends a linear form to its bundled Koszul algebra. -/
@[simp]
theorem commMonFunctor_obj (phi : LinearForm O) :
    (commMonFunctor O).obj phi = commMon O phi.hom := sorry

/-- On morphisms, the commutative Koszul-algebra functor uses the canonical Koszul-algebra
map. -/
@[simp]
theorem commMonFunctor_map {phi psi : LinearForm O} (f : phi ⟶ psi) :
    (commMonFunctor O).map f = commMonMap O f := sorry

/-- Forgetting the algebra structure from the Koszul-algebra functor gives the Koszul
chain-complex functor. -/
theorem commMonFunctor_comp_forget :
    commMonFunctor O ⋙
        CommMon.forget (ChainComplex (ringedSiteModuleCategory J O) ℕ) =
      complexFunctor O := sorry

end SheafOfModules.RingedSite.Koszul
