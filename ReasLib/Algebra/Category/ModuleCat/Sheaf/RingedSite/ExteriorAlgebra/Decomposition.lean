/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra.Decomposition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.CategoryTheory.GradedObject.Total.PreservesCoproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# The exterior algebra as the total of exterior powers

The sectionwise exterior-algebra construction followed by sheafification is naturally the
underlying module of the canonical total exterior-algebra monoid. Every comparison component is
an explicit composite of the presheaf decomposition and coproduct-preservation isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The explicit comparison between the sheafified sectionwise exterior algebra and the
underlying object of the total exterior monoid. -/
@[stacks 01CF "exterior algebra as the total of exterior powers"]
noncomputable def decompositionAppIso
    (F : ringedSiteModuleCategory J O) :
    (functor O).obj F ≅ ((monFunctor O).obj F).X :=
  (moduleSheafification O).mapIso
      (PresheafOfModules.ExteriorAlgebra.decompositionIso O.obj F.val) ≪≫
    (GradedObject.Total.mapIso (I := ℕ) (moduleSheafification O)).app
      (PresheafOfModules.ExteriorPower.Total.gradedObject O.obj F.val) ≪≫
    Limits.Sigma.mapIso (fun n : ℕ ↦ ExteriorPower.sheafificationIso O F n) ≪≫
    (totalMonIso O).app F

/-- The exterior-algebra comparison components are natural in the module sheaf. -/
@[stacks 01CF "exterior-algebra sheaf decomposition forward naturality"]
theorem decompositionAppIso_hom_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (functor O).map f ≫ (decompositionAppIso O G).hom =
      (decompositionAppIso O F).hom ≫
        (monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O)).map f := sorry

/-- The inverse exterior-algebra comparison components are natural in the module sheaf. -/
@[stacks 01CF "exterior-algebra sheaf decomposition inverse naturality"]
theorem decompositionAppIso_inv_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O)).map f ≫
        (decompositionAppIso O G).inv =
      (decompositionAppIso O F).inv ≫ (functor O).map f := sorry

/-- The forward exterior-algebra comparison components form a natural transformation to the
underlying total exterior-algebra monoid. -/
@[stacks 01CF "exterior-algebra sheaf decomposition natural transformation"]
noncomputable def decompositionNatTrans :
    functor O ⟶ monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O) where
  app F := (decompositionAppIso O F).hom
  naturality _ _ f := decompositionAppIso_hom_naturality O f

/-- The inverse exterior-algebra comparison components form a natural transformation from the
underlying total exterior-algebra monoid. -/
@[stacks 01CF "inverse exterior-algebra sheaf decomposition natural transformation"]
noncomputable def decompositionInvNatTrans :
    monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O) ⟶ functor O where
  app F := (decompositionAppIso O F).inv
  naturality _ _ f := decompositionAppIso_inv_naturality O f

/-- A component of the forward exterior-algebra decomposition transformation is the forward
objectwise comparison. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition natural transformation component"]
theorem decompositionNatTrans_app
    (F : ringedSiteModuleCategory J O) :
    (decompositionNatTrans O).app F = (decompositionAppIso O F).hom := sorry

/-- A component of the inverse exterior-algebra decomposition transformation is the inverse
objectwise comparison. -/
@[simp, stacks 01CF "inverse exterior-algebra sheaf decomposition natural transformation component"]
theorem decompositionInvNatTrans_app
    (F : ringedSiteModuleCategory J O) :
    (decompositionInvNatTrans O).app F = (decompositionAppIso O F).inv := sorry

/-- The forward exterior-algebra decomposition transformation followed by its inverse is the
identity. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition forward-inverse law"]
theorem decompositionNatTrans_hom_inv_id :
    decompositionNatTrans O ≫ decompositionInvNatTrans O = 𝟙 _ := sorry

/-- The inverse exterior-algebra decomposition transformation followed by the forward one is
the identity. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition inverse-forward law"]
theorem decompositionNatTrans_inv_hom_id :
    decompositionInvNatTrans O ≫ decompositionNatTrans O = 𝟙 _ := sorry

/-- The traditional exterior-algebra sheaf functor is naturally the underlying functor of the
canonical total exterior-algebra monoid. -/
@[stacks 01CF "natural exterior-algebra total decomposition"]
noncomputable def decompositionIso :
    functor O ≅ monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O) where
  hom := decompositionNatTrans O
  inv := decompositionInvNatTrans O
  hom_inv_id := decompositionNatTrans_hom_inv_id O
  inv_hom_id := decompositionNatTrans_inv_hom_id O

/-- A component of the natural exterior-algebra decomposition is the explicit objectwise
comparison isomorphism. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition natural isomorphism component"]
theorem decompositionIso_app
    (F : ringedSiteModuleCategory J O) :
    (decompositionIso O).app F = decompositionAppIso O F := sorry

/-- The forward transformation of the natural exterior-algebra decomposition is explicit. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition natural isomorphism hom"]
theorem decompositionIso_hom :
    (decompositionIso O).hom = decompositionNatTrans O := sorry

/-- The inverse transformation of the natural exterior-algebra decomposition is explicit. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition natural isomorphism inverse"]
theorem decompositionIso_inv :
    (decompositionIso O).inv = decompositionInvNatTrans O := sorry

/-- A component of the natural exterior-algebra decomposition is the explicit comparison. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition natural isomorphism hom component"]
theorem decompositionIso_hom_app
    (F : ringedSiteModuleCategory J O) :
    (decompositionIso O).hom.app F = (decompositionAppIso O F).hom := sorry

/-- An inverse component of the natural exterior-algebra decomposition is the inverse explicit
comparison. -/
@[simp, stacks 01CF "exterior-algebra sheaf decomposition natural isomorphism inverse component"]
theorem decompositionIso_inv_app
    (F : ringedSiteModuleCategory J O) :
    (decompositionIso O).inv.app F = (decompositionAppIso O F).inv := sorry

/-- The sheafified degree-`n` homogeneous inclusion into the traditional exterior-algebra
sheaf. -/
@[stacks 01CF "homogeneous inclusion into an exterior-algebra sheaf"]
noncomputable def powerι
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    ExteriorPower.sheaf O F n ⟶ sheaf O F :=
  (moduleSheafification O).map
    (PresheafOfModules.ExteriorAlgebra.powerι O.obj F.val n)

/-- Exterior-power sheaf maps commute with homogeneous inclusions. -/
@[reassoc]
theorem map_powerι
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) (n : ℕ) :
    ExteriorPower.map O f n ≫ powerι O G n =
      powerι O F n ≫ map O f := sorry

/-- For fixed degree, homogeneous inclusion is natural in the module sheaf. -/
@[stacks 01CF "natural homogeneous inclusion into an exterior-algebra sheaf"]
noncomputable def powerιNatTrans (n : ℕ) :
    ExteriorPower.functor O n ⟶ functor O where
  app F := powerι O F n
  naturality _ _ f := map_powerι O f n

/-- A component of the fixed-degree sheaf inclusion is `powerι`. -/
@[simp]
theorem powerιNatTrans_app
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    (powerιNatTrans O n).app F = powerι O F n := sorry

/-- Under the total decomposition, a homogeneous exterior-power inclusion is the coproduct
inclusion. -/
@[reassoc (attr := simp)]
theorem powerι_decompositionAppIso_hom
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    powerι O F n ≫ (decompositionAppIso O F).hom =
      Limits.Sigma.ι (ExteriorPower.gradedObject O F) n := sorry

/-- The inverse total decomposition restricts on a homogeneous summand to its inclusion into
the traditional exterior-algebra sheaf. -/
@[reassoc (attr := simp)]
theorem ι_decompositionAppIso_inv
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    Limits.Sigma.ι (ExteriorPower.gradedObject O F) n ≫
        (decompositionAppIso O F).inv =
      powerι O F n := sorry

/-- The degree-one exterior-power inclusion is the traditional exterior-algebra generator. -/
@[reassoc (attr := simp)]
theorem degreeOne_powerι (F : ringedSiteModuleCategory J O) :
    ExteriorPower.degreeOne O F ≫ powerι O F 1 = ι O F := sorry

/-- Under the total decomposition, the traditional exterior-algebra generator lands in the
degree-one summand. -/
@[reassoc (attr := simp)]
theorem ι_decompositionAppIso_hom
    (F : ringedSiteModuleCategory J O) :
    ι O F ≫ (decompositionAppIso O F).hom =
      ExteriorPower.degreeOne O F ≫
        Limits.Sigma.ι (ExteriorPower.gradedObject O F) 1 := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
