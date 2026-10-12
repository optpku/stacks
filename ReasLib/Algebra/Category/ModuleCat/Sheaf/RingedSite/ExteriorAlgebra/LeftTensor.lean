/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra.LeftTensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-one multiplication on exterior-algebra sheaves

This leaf transports sectionwise degree-one multiplication through module sheafification.  It is
the topology-independent source of the exterior-algebra action used by determinant sheaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The canonical degree-one left multiplication morphism
`F ⊗ Λ(F) ⟶ Λ(F)` on a commutative ringed site. -/
@[stacks 0FJN "degree-one exterior multiplication on a ringed site"]
noncomputable def leftTensorMap (F : ringedSiteModuleCategory J 𝒪) :
    tensorObj F (sheaf 𝒪 F) ⟶ sheaf 𝒪 F :=
  tensorHom (moduleSheafificationValIso 𝒪 F).inv (𝟙 (sheaf 𝒪 F)) ≫
    (ModuleSheafification.tensorIso 𝒪 F.val (presheaf 𝒪 F)).hom ≫
    (moduleSheafification 𝒪).map
      (PresheafOfModules.ExteriorAlgebra.leftTensorHom 𝒪.obj F.val)

/-- Degree-one multiplication on exterior-algebra sheaves is natural in the module sheaf. -/
theorem leftTensorMap_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    tensorHom f (map 𝒪 f) ≫ leftTensorMap 𝒪 G =
      leftTensorMap 𝒪 F ≫ map 𝒪 f := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
