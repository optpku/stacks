module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# First exterior powers of module sheaves

Sheafifying the sectionwise degree-one map identifies a module sheaf with its first exterior
power, functorially over any commutative ringed site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- A module sheaf is canonically isomorphic to its first exterior-power sheaf. -/
@[stacks 01CF "module sheaf as its first exterior power"]
noncomputable def degreeOneIso (F : ringedSiteModuleCategory J O) :
    F ≅ sheaf O F 1 :=
  (moduleSheafificationValIso O F).symm ≪≫
    (moduleSheafification O).mapIso
      (PresheafOfModules.ExteriorPower.degreeOneIso O.obj F.val)

/-- The canonical morphism from a module sheaf to its first exterior-power sheaf. -/
noncomputable def degreeOne (F : ringedSiteModuleCategory J O) :
    F ⟶ sheaf O F 1 :=
  (degreeOneIso O F).hom

/-- The forward map of the degree-one isomorphism is `degreeOne`. -/
@[simp]
theorem degreeOneIso_hom (F : ringedSiteModuleCategory J O) :
    (degreeOneIso O F).hom = degreeOne O F := sorry

/-- The canonical degree-one exterior-power morphism is an isomorphism. -/
instance degreeOne_isIso (F : ringedSiteModuleCategory J O) :
    IsIso (degreeOne O F) := sorry

/-- The sheaf degree-one map is the sheafification of the sectionwise degree-one map, after
identifying a sheaf with the sheafification of its underlying presheaf. -/
theorem degreeOne_eq (F : ringedSiteModuleCategory J O) :
    degreeOne O F =
      (moduleSheafificationValIso O F).inv ≫
        (moduleSheafification O).map
          (PresheafOfModules.ExteriorPower.degreeOne O.obj F.val) := sorry

/-- The inverse sheaf degree-one isomorphism is obtained by sheafifying the inverse sectionwise
isomorphism and then applying the sheafification comparison. -/
theorem degreeOneIso_inv (F : ringedSiteModuleCategory J O) :
    (degreeOneIso O F).inv =
      (moduleSheafification O).map
          (PresheafOfModules.ExteriorPower.degreeOneIso O.obj F.val).inv ≫
        (moduleSheafificationValIso O F).hom := sorry

/-- First exterior-power maps are natural in the module sheaf. -/
@[reassoc, stacks 01CF "first exterior power map naturality"]
theorem degreeOne_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    f ≫ degreeOne O G = degreeOne O F ≫ map O f 1 := sorry

/-- The inverse first-exterior-power maps are natural in the module sheaf. -/
@[stacks 01CF "inverse first exterior power map naturality"]
theorem degreeOneIso_inv_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    map O f 1 ≫ (degreeOneIso O G).inv =
      (degreeOneIso O F).inv ≫ f := sorry

/-- The degree-one maps form the forward natural transformation from module sheaves to their
first exterior powers. -/
@[stacks 01CF "forward first exterior power natural transformation"]
noncomputable def degreeOneNatTrans :
    (𝟭 _ : ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O) ⟶
      functor O 1 where
  app F := degreeOne O F
  naturality _ _ f := degreeOne_naturality O f

/-- The inverse objectwise degree-one maps form the reverse natural transformation. -/
@[stacks 01CF "inverse first exterior power natural transformation"]
noncomputable def degreeOneInvNatTrans :
    functor O 1 ⟶
      (𝟭 _ : ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O) where
  app F := (degreeOneIso O F).inv
  naturality _ _ f := degreeOneIso_inv_naturality O f

/-- A component of the forward degree-one natural transformation is the canonical degree-one
map. -/
@[simp, stacks 01CF "forward first exterior power natural transformation component"]
theorem degreeOneNatTrans_app (F : ringedSiteModuleCategory J O) :
    (degreeOneNatTrans O).app F = degreeOne O F := sorry

/-- A component of the inverse degree-one natural transformation is the inverse objectwise
degree-one map. -/
@[simp, stacks 01CF "inverse first exterior power natural transformation component"]
theorem degreeOneInvNatTrans_app (F : ringedSiteModuleCategory J O) :
    (degreeOneInvNatTrans O).app F = (degreeOneIso O F).inv := sorry

/-- The forward degree-one natural transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "first exterior power natural transformation forward-inverse law"]
theorem degreeOneNatTrans_hom_inv_id :
    degreeOneNatTrans O ≫ degreeOneInvNatTrans O = 𝟙 _ := sorry

/-- The inverse degree-one natural transformation followed by the forward one is the identity. -/
@[simp, stacks 01CF "first exterior power natural transformation inverse-forward law"]
theorem degreeOneNatTrans_inv_hom_id :
    degreeOneInvNatTrans O ≫ degreeOneNatTrans O = 𝟙 _ := sorry

/-- Module sheaves are naturally isomorphic to their first exterior powers. -/
@[stacks 01CF "natural first exterior power of module sheaves"]
noncomputable def degreeOneNatIso :
    (𝟭 _ : ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O) ≅
      functor O 1 :=
  { hom := degreeOneNatTrans O
    inv := degreeOneInvNatTrans O
    hom_inv_id := degreeOneNatTrans_hom_inv_id O
    inv_hom_id := degreeOneNatTrans_inv_hom_id O }

/-- A component of `degreeOneNatIso` is the objectwise first-exterior-power isomorphism. -/
@[simp, stacks 01CF "first exterior power natural isomorphism component"]
theorem degreeOneNatIso_app (F : ringedSiteModuleCategory J O) :
    (degreeOneNatIso O).app F = degreeOneIso O F := sorry

/-- The forward transformation of `degreeOneNatIso` is the explicit degree-one family. -/
@[simp, stacks 01CF "first exterior power natural isomorphism hom"]
theorem degreeOneNatIso_hom :
    (degreeOneNatIso O).hom = degreeOneNatTrans O := sorry

/-- The inverse transformation of `degreeOneNatIso` is the explicit inverse family. -/
@[simp, stacks 01CF "first exterior power natural isomorphism inverse"]
theorem degreeOneNatIso_inv :
    (degreeOneNatIso O).inv = degreeOneInvNatTrans O := sorry

/-- The forward component of `degreeOneNatIso` is the canonical degree-one map. -/
@[simp, stacks 01CF "first exterior power natural isomorphism hom component"]
theorem degreeOneNatIso_hom_app (F : ringedSiteModuleCategory J O) :
    (degreeOneNatIso O).hom.app F = degreeOne O F := sorry

/-- The inverse component of `degreeOneNatIso` is the inverse objectwise map. -/
@[simp, stacks 01CF "first exterior power natural isomorphism inverse component"]
theorem degreeOneNatIso_inv_app (F : ringedSiteModuleCategory J O) :
    (degreeOneNatIso O).inv.app F = (degreeOneIso O F).inv := sorry

end SheafOfModules.RingedSite.ExteriorPower

