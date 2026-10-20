module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of same-site extension of scalars

For a morphism of sheaves of commutative rings on a topological space, extension of scalars
commutes with taking stalks.  The public owner is a natural transformation whose components point
from scalar extension of the original stalk to the stalk of the sheaf-level scalar extension.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf.ChangeOfRings.Stalk

variable {X : TopCat.{u}} {O O' : X.Sheaf CommRingCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The morphism on stalk rings induced by a same-space morphism of commutative-ring sheaves. -/
abbrev ringMap (p : O ⟶ O') (x : X) : O.presheaf.stalk x ⟶ O'.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map p.hom

/-- First take the stalk of a module sheaf and then extend scalars along the induced stalk-ring
morphism. -/
noncomputable abbrev source (p : O ⟶ O') (x : X) :
    SheafOfModules (ringSheafOfComm O) ⥤ ModuleCat (O'.presheaf.stalk x) :=
  SheafOfModules.stalkFunctorOfCommRing O x ⋙
    ModuleCat.extendScalars (ringMap p x).hom

/-- First extend scalars along a morphism of ring sheaves and then take the stalk. -/
noncomputable abbrev target (p : O ⟶ O') (x : X) :
    SheafOfModules (ringSheafOfComm O) ⥤ ModuleCat (O'.presheaf.stalk x) :=
  SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap p) ⋙
    SheafOfModules.stalkFunctorOfCommRing O' x

/-- The explicit pullback construction underlying same-site extension of scalars. -/
noncomputable abbrev construction (p : O ⟶ O')
    (F : SheafOfModules (ringSheafOfComm O)) :
    SheafOfModules (ringSheafOfComm O') :=
  (PresheafOfModules.sheafification (𝟙 (ringSheafOfComm O').obj)).obj
    ((PresheafOfModules.pullback
      (TopCat.Presheaf.commRingPresheafHomOverId p.hom)).obj F.val)

/-- The canonical comparison from the explicit pullback construction to the chosen
extension-of-scalars functor. -/
noncomputable def constructionToExtension (p : O ⟶ O')
    (F : SheafOfModules (ringSheafOfComm O)) :
    construction p F ⟶
      (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap p)).obj F :=
  (SheafOfModules.pullbackIso (ringedSiteStructureMap p)).inv.app F ≫
    (SheafOfModules.ChangeOfRings.pullbackIso (ringSheafMap p)).hom.app F

/-- The explicit inverse from the chosen extension-of-scalars functor to its pullback
construction. -/
noncomputable def constructionToExtensionInv (p : O ⟶ O')
    (F : SheafOfModules (ringSheafOfComm O)) :
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap p)).obj F ⟶
      construction p F :=
  (SheafOfModules.ChangeOfRings.pullbackIso (ringSheafMap p)).inv.app F ≫
    (SheafOfModules.pullbackIso (ringedSiteStructureMap p)).hom.app F

/-- The pullback construction comparison followed by its inverse is the identity. -/
@[simp]
theorem constructionToExtension_hom_inv_id (p : O ⟶ O')
    (F : SheafOfModules (ringSheafOfComm O)) :
    constructionToExtension p F ≫ constructionToExtensionInv p F = 𝟙 _ := sorry

/-- The inverse pullback construction comparison followed by the comparison is the identity. -/
@[simp]
theorem constructionToExtension_inv_hom_id (p : O ⟶ O')
    (F : SheafOfModules (ringSheafOfComm O)) :
    constructionToExtensionInv p F ≫ constructionToExtension p F = 𝟙 _ := sorry

/-- The canonical isomorphism from the explicit pullback construction to the chosen
extension-of-scalars functor. -/
noncomputable def constructionToExtensionIso (p : O ⟶ O')
    (F : SheafOfModules (ringSheafOfComm O)) :
    construction p F ≅
      (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap p)).obj F where
  hom := constructionToExtension p F
  inv := constructionToExtensionInv p F
  hom_inv_id := constructionToExtension_hom_inv_id p F
  inv_hom_id := constructionToExtension_inv_hom_id p F

/-- The component of the canonical comparison between stalkwise and sheaf-level extension of
scalars. -/
noncomputable def comparisonApp (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (source p x).obj F ⟶ (target p x).obj F :=
  TopCat.Sheaf.moduleBaseChangeStalkComparison p F x ≫
    (SheafOfModules.stalkFunctorOfCommRing O' x).map
      (constructionToExtension p F)

/-- The stalkwise scalar-extension comparisons are natural in the module sheaf. -/
theorem comparison_naturality (p : O ⟶ O') (x : X)
    {F G : SheafOfModules (ringSheafOfComm O)} (f : F ⟶ G) :
    (source p x).map f ≫ comparisonApp p x G =
      comparisonApp p x F ≫ (target p x).map f := sorry

/-- Same-site extension of scalars commutes with taking stalks. -/
@[stacks 0D09 "same-site scalar extension commutes with stalks"]
noncomputable def comparison (p : O ⟶ O') (x : X) : source p x ⟶ target p x where
  app := comparisonApp p x
  naturality _ _ f := comparison_naturality p x f

/-- The explicit inverse component of the same-site scalar-extension stalk comparison. -/
@[stacks 0D09 "inverse same-site scalar-extension stalk comparison"]
noncomputable def comparisonInvApp (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (target p x).obj F ⟶ (source p x).obj F :=
  (SheafOfModules.stalkFunctorOfCommRing O' x).map
      (constructionToExtensionInv p F) ≫
    TopCat.Sheaf.moduleBaseChangeStalkComparisonInv p F x

/-- A comparison component followed by its explicit inverse is the identity. -/
@[simp]
theorem comparisonApp_hom_inv_id (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    comparisonApp p x F ≫ comparisonInvApp p x F = 𝟙 _ := sorry

/-- An explicit inverse component followed by the comparison is the identity. -/
@[simp]
theorem comparisonApp_inv_hom_id (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    comparisonInvApp p x F ≫ comparisonApp p x F = 𝟙 _ := sorry

/-- A component of the same-site scalar-extension stalk comparison as literal isomorphism
data. -/
@[stacks 0D09 "same-site scalar-extension stalk comparison isomorphism"]
noncomputable def comparisonIso (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (source p x).obj F ≅ (target p x).obj F where
  hom := comparisonApp p x F
  inv := comparisonInvApp p x F
  hom_inv_id := comparisonApp_hom_inv_id p x F
  inv_hom_id := comparisonApp_inv_hom_id p x F

/-- Every component of the same-site scalar-extension stalk comparison is an isomorphism. -/
@[stacks 0D09 "same-site scalar-extension stalk comparison is an isomorphism", instance]
instance comparisonApp_isIso (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    IsIso ((comparison p x).app F) :=
  (comparisonIso p x F).isIso_hom

/-- The forward map of a component comparison is the explicit stalk comparison. -/
@[stacks 0D09 "same-site scalar-extension stalk comparison isomorphism hom", simp]
theorem comparisonIso_hom (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (comparisonIso p x F).hom = comparisonApp p x F := sorry

/-- The inverse map of a component comparison is the explicit inverse component. -/
@[stacks 0D09 "same-site scalar-extension stalk comparison isomorphism inverse", simp]
theorem comparisonIso_inv (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (comparisonIso p x F).inv = comparisonInvApp p x F := sorry

/-- The inverse comparison components are natural in the module sheaf. -/
theorem comparisonInv_naturality (p : O ⟶ O') (x : X)
    {F G : SheafOfModules (ringSheafOfComm O)} (f : F ⟶ G) :
    (target p x).map f ≫ comparisonInvApp p x G =
      comparisonInvApp p x F ≫ (source p x).map f := sorry

/-- The explicit inverse natural transformation for same-site scalar extension on stalks. -/
@[stacks 0D09 "inverse same-site scalar extension stalk comparison"]
noncomputable def comparisonInv (p : O ⟶ O') (x : X) : target p x ⟶ source p x where
  app := comparisonInvApp p x
  naturality _ _ f := comparisonInv_naturality p x f

/-- The comparison followed by its inverse natural transformation is the identity. -/
@[simp]
theorem comparison_hom_inv_id (p : O ⟶ O') (x : X) :
    comparison p x ≫ comparisonInv p x = 𝟙 _ := sorry

/-- The inverse followed by the comparison natural transformation is the identity. -/
@[simp]
theorem comparison_inv_hom_id (p : O ⟶ O') (x : X) :
    comparisonInv p x ≫ comparison p x = 𝟙 _ := sorry

/-- Same-site extension of scalars commutes with stalks as a natural isomorphism in the module
sheaf. -/
@[stacks 0D09 "same-site scalar extension commutes with stalks naturally"]
noncomputable def comparisonNatIso (p : O ⟶ O') (x : X) :
    source p x ≅ target p x where
  hom := comparison p x
  inv := comparisonInv p x
  hom_inv_id := comparison_hom_inv_id p x
  inv_hom_id := comparison_inv_hom_id p x

/-- The natural comparison between stalkwise and sheaf-level scalar extension is an
isomorphism. -/
@[stacks 0D09 "same-site scalar-extension stalk natural transformation is an isomorphism"]
instance comparison_isIso (p : O ⟶ O') (x : X) :
    IsIso (comparison p x) := (comparisonNatIso p x).isIso_hom

/-- The forward natural transformation of `comparisonNatIso` is `comparison`. -/
@[stacks 0D09 "same-site scalar-extension stalk natural isomorphism hom", simp]
theorem comparisonNatIso_hom (p : O ⟶ O') (x : X) :
    (comparisonNatIso p x).hom = comparison p x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit inverse. -/
@[stacks 0D09 "same-site scalar-extension stalk natural isomorphism inverse", simp]
theorem comparisonNatIso_inv (p : O ⟶ O') (x : X) :
    (comparisonNatIso p x).inv = comparisonInv p x := sorry

/-- A component of `comparisonNatIso` is the corresponding pointwise comparison isomorphism. -/
@[stacks 0D09 "same-site scalar-extension stalk natural isomorphism component", simp]
theorem comparisonNatIso_app (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (comparisonNatIso p x).app F = comparisonIso p x F := sorry

/-- The forward component of `comparisonNatIso` is the explicit stalk comparison. -/
@[stacks 0D09 "same-site scalar-extension stalk natural isomorphism hom component", simp]
theorem comparisonNatIso_hom_app (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (comparisonNatIso p x).hom.app F = comparisonApp p x F := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[stacks 0D09 "same-site scalar-extension stalk natural isomorphism inverse component", simp]
theorem comparisonNatIso_inv_app (p : O ⟶ O') (x : X)
    (F : SheafOfModules (ringSheafOfComm O)) :
    (comparisonNatIso p x).inv.app F = comparisonInvApp p x F := sorry

end TopCat.Sheaf.ChangeOfRings.Stalk
