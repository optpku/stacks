/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Biproduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Multiplication.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of binary biproducts on a ringed site

The forward determinant product morphism is defined for arbitrary module sheaves.  It tensors the
two determinant inclusions, maps both exterior algebras into the exterior algebra of the
biproduct, multiplies there, and then uses the determinant kernel's universal property.  Finite
local freeness is needed only to assert that this morphism is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Determinant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The ambient exterior-algebra morphism underlying the determinant product morphism. -/
@[stacks 0B38 "ambient determinant product morphism on a ringed site"]
noncomputable def prodAmbientHom
    (F G : ringedSiteModuleCategory J O) :
    tensorObj (sheaf F) (sheaf G) ⟶ ExteriorAlgebra.sheaf O (F ⊞ G) :=
  tensorHom (ι F) (ι G) ≫
    tensorHom
      (ExteriorAlgebra.map O (biprod.inl : F ⟶ F ⊞ G))
      (ExteriorAlgebra.map O (biprod.inr : G ⟶ F ⊞ G)) ≫
    ExteriorAlgebra.mul O (F ⊞ G)

/-- The ambient determinant product morphism is annihilated by degree-one multiplication on the
biproduct. -/
@[reassoc, stacks 0B38 "determinant product morphism lands in the determinant"]
theorem prodAmbientHom_comp_action
    (F G : ringedSiteModuleCategory J O) :
    prodAmbientHom O F G ≫ action (F ⊞ G) = 0 := sorry

/-- The determinant product morphism for arbitrary module sheaves on a commutative ringed site. -/
@[stacks 0B38 "determinant product morphism on a ringed site"]
noncomputable def prodHom
    (F G : ringedSiteModuleCategory J O) :
    tensorObj (sheaf F) (sheaf G) ⟶ sheaf (F ⊞ G) :=
  lift (F ⊞ G) (prodAmbientHom O F G) (prodAmbientHom_comp_action O F G)

/-- The determinant product lift recovers the ambient exterior-algebra morphism after the
determinant inclusion. -/
@[reassoc, stacks 0B38 "determinant product morphism inclusion equation"]
theorem prodHom_ι
    (F G : ringedSiteModuleCategory J O) :
    prodHom O F G ≫ ι (F ⊞ G) = prodAmbientHom O F G := sorry

/-- The determinant product morphism is natural in a pair of module-sheaf isomorphisms and the
induced biproduct isomorphism. -/
@[reassoc, stacks 0B38 "naturality of the determinant biproduct morphism"]
theorem prodHom_naturality
    {F F' G G' : ringedSiteModuleCategory J O}
    (e : F ≅ F') (f : G ≅ G') :
    tensorHom (mapIso e).hom (mapIso f).hom ≫ prodHom O F' G' =
      prodHom O F G ≫ (mapIso (biprod.mapIso e f)).hom := sorry

section IsIso

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The determinant product morphism is an isomorphism for finite locally free module sheaves. -/
@[stacks 0B38 "determinant of a finite locally free biproduct is a tensor product"]
instance prodHom_isIso
    (F G : ringedSiteModuleCategory J O)
    [SheafOfModules.IsFiniteLocallyFree F]
    [SheafOfModules.IsFiniteLocallyFree G] :
    IsIso (prodHom O F G) := sorry

end IsIso

end SheafOfModules.RingedSite.Determinant
