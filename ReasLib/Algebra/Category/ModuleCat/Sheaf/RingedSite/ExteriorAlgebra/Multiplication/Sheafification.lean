/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on exterior-algebra sheaves

Exterior-algebra multiplication is obtained directly by sheafifying the objectwise multiplication
morphism.  This sheafification leaf is independent of the graded-total presentation of the
exterior algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The multiplicative unit of the exterior-algebra sheaf. -/
@[stacks 01CF "unit of an exterior-algebra sheaf"]
noncomputable def one (F : ringedSiteModuleCategory J O) :
    𝟙_ (ringedSiteModuleCategory J O) ⟶ sheaf O F :=
  Functor.LaxMonoidal.ε (moduleSheafification O) ≫
    (moduleSheafification O).map
      (PresheafOfModules.ExteriorAlgebra.oneHom O.obj F.val)

/-- Multiplication on the exterior-algebra sheaf, descended directly from objectwise exterior
algebra multiplication. -/
@[stacks 01CF "multiplication on an exterior-algebra sheaf"]
noncomputable def mul (F : ringedSiteModuleCategory J O) :
    tensorObj (sheaf O F) (sheaf O F) ⟶ sheaf O F :=
  (ModuleSheafification.tensorIso O (presheaf O F) (presheaf O F)).hom ≫
    (moduleSheafification O).map
      (PresheafOfModules.ExteriorAlgebra.mulHom O.obj F.val)

/-- Multiplication on exterior-algebra sheaves is natural in the module sheaf. -/
@[reassoc, stacks 01CF "naturality of exterior-algebra sheaf multiplication"]
theorem mul_naturality {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    tensorHom (map O f) (map O f) ≫ mul O G = mul O F ≫ map O f := sorry

/-- Exterior-algebra sheaf units are natural in the module sheaf. -/
@[reassoc, stacks 01CF "naturality of exterior-algebra sheaf units"]
theorem one_naturality {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    one O F ≫ map O f = one O G := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
