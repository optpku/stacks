/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# First symmetric powers of module sheaves

Sheafifying the sectionwise degree-one isomorphism identifies a module sheaf with its first
symmetric power, naturally over every commutative ringed site.
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

/-- A module sheaf is canonically isomorphic to its first symmetric-power sheaf. -/
@[stacks 01CF "module sheaf as its first symmetric power"]
noncomputable def degreeOneIso (F : ringedSiteModuleCategory J 𝒪) :
    F ≅ sheaf 𝒪 F 1 :=
  (moduleSheafificationValIso 𝒪 F).symm ≪≫
    (moduleSheafification 𝒪).mapIso
      (PresheafOfModules.SymmetricPower.degreeOneIso 𝒪.obj F.val)

/-- The canonical morphism from a module sheaf to its first symmetric-power sheaf. -/
@[stacks 01CF "first symmetric power module-sheaf map"]
noncomputable def degreeOne (F : ringedSiteModuleCategory J 𝒪) :
    F ⟶ sheaf 𝒪 F 1 :=
  (degreeOneIso 𝒪 F).hom

/-- The forward map of the first-symmetric-power isomorphism is `degreeOne`. -/
@[simp, stacks 01CF "first symmetric power isomorphism hom"]
theorem degreeOneIso_hom (F : ringedSiteModuleCategory J 𝒪) :
    (degreeOneIso 𝒪 F).hom = degreeOne 𝒪 F := sorry

/-- The canonical degree-one symmetric-power morphism is an isomorphism. -/
instance degreeOne_isIso (F : ringedSiteModuleCategory J 𝒪) :
    IsIso (degreeOne 𝒪 F) := sorry

/-- The sheaf degree-one map is the sheafification of the sectionwise degree-one map, after
identifying a sheaf with the sheafification of its underlying presheaf. -/
@[stacks 01CF "first symmetric power map as sheafification"]
theorem degreeOne_eq (F : ringedSiteModuleCategory J 𝒪) :
    degreeOne 𝒪 F =
      (moduleSheafificationValIso 𝒪 F).inv ≫
        (moduleSheafification 𝒪).map
          (PresheafOfModules.SymmetricPower.degreeOne 𝒪.obj F.val) := sorry

/-- The inverse sheaf degree-one isomorphism is obtained by sheafifying the inverse sectionwise
isomorphism and then applying the sheafification comparison. -/
@[stacks 01CF "inverse first symmetric power map as sheafification"]
theorem degreeOneIso_inv (F : ringedSiteModuleCategory J 𝒪) :
    (degreeOneIso 𝒪 F).inv =
      (moduleSheafification 𝒪).map
          (PresheafOfModules.SymmetricPower.degreeOneIso 𝒪.obj F.val).inv ≫
        (moduleSheafificationValIso 𝒪 F).hom := sorry

/-- First symmetric-power maps are natural in the module sheaf. -/
@[reassoc, stacks 01CF "first symmetric power map naturality"]
theorem degreeOne_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    f ≫ degreeOne 𝒪 G = degreeOne 𝒪 F ≫ map 𝒪 f 1 := sorry

/-- The inverse first-symmetric-power maps are natural in the module sheaf. -/
@[stacks 01CF "inverse first symmetric power map naturality"]
theorem degreeOneIso_inv_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    map 𝒪 f 1 ≫ (degreeOneIso 𝒪 G).inv =
      (degreeOneIso 𝒪 F).inv ≫ f := sorry

/-- The degree-one maps form the forward natural transformation from module sheaves to their
first symmetric powers. -/
@[stacks 01CF "forward first symmetric power natural transformation"]
noncomputable def degreeOneNatTrans :
    (𝟭 _ : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪) ⟶
      functor 𝒪 1 where
  app F := degreeOne 𝒪 F
  naturality _ _ f := degreeOne_naturality 𝒪 f

/-- The inverse objectwise degree-one maps form the reverse natural transformation. -/
@[stacks 01CF "inverse first symmetric power natural transformation"]
noncomputable def degreeOneInvNatTrans :
    functor 𝒪 1 ⟶
      (𝟭 _ : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪) where
  app F := (degreeOneIso 𝒪 F).inv
  naturality _ _ f := degreeOneIso_inv_naturality 𝒪 f

/-- A component of the forward natural transformation is the canonical degree-one map. -/
@[simp, stacks 01CF "forward first symmetric power natural transformation component"]
theorem degreeOneNatTrans_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeOneNatTrans 𝒪).app F = degreeOne 𝒪 F := sorry

/-- A component of the inverse natural transformation is the inverse objectwise map. -/
@[simp, stacks 01CF "inverse first symmetric power natural transformation component"]
theorem degreeOneInvNatTrans_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeOneInvNatTrans 𝒪).app F = (degreeOneIso 𝒪 F).inv := sorry

/-- The forward degree-one natural transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "first symmetric power natural transformation forward-inverse law"]
theorem degreeOneNatTrans_hom_inv_id :
    degreeOneNatTrans 𝒪 ≫ degreeOneInvNatTrans 𝒪 = 𝟙 _ := sorry

/-- The inverse degree-one natural transformation followed by the forward one is the identity. -/
@[simp, stacks 01CF "first symmetric power natural transformation inverse-forward law"]
theorem degreeOneNatTrans_inv_hom_id :
    degreeOneInvNatTrans 𝒪 ≫ degreeOneNatTrans 𝒪 = 𝟙 _ := sorry

/-- Module sheaves are naturally isomorphic to their first symmetric powers. -/
@[stacks 01CF "natural first symmetric power of module sheaves"]
noncomputable def degreeOneNatIso :
    (𝟭 _ : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪) ≅
      functor 𝒪 1 :=
  { hom := degreeOneNatTrans 𝒪
    inv := degreeOneInvNatTrans 𝒪
    hom_inv_id := degreeOneNatTrans_hom_inv_id 𝒪
    inv_hom_id := degreeOneNatTrans_inv_hom_id 𝒪 }

/-- A component of `degreeOneNatIso` is the objectwise first-symmetric-power isomorphism. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism component"]
theorem degreeOneNatIso_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeOneNatIso 𝒪).app F = degreeOneIso 𝒪 F := sorry

/-- The forward transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism hom"]
theorem degreeOneNatIso_hom :
    (degreeOneNatIso 𝒪).hom = degreeOneNatTrans 𝒪 := sorry

/-- The inverse transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism inverse"]
theorem degreeOneNatIso_inv :
    (degreeOneNatIso 𝒪).inv = degreeOneInvNatTrans 𝒪 := sorry

/-- The forward component of `degreeOneNatIso` is the canonical degree-one map. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism hom component"]
theorem degreeOneNatIso_hom_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeOneNatIso 𝒪).hom.app F = degreeOne 𝒪 F := sorry

/-- The inverse component of `degreeOneNatIso` is the inverse objectwise map. -/
@[simp, stacks 01CF "first symmetric power natural isomorphism inverse component"]
theorem degreeOneNatIso_inv_app (F : ringedSiteModuleCategory J 𝒪) :
    (degreeOneNatIso 𝒪).inv.app F = (degreeOneIso 𝒪 F).inv := sorry

end SheafOfModules.RingedSite.SymmetricPower
