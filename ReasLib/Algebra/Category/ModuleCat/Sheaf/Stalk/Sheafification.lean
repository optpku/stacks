/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Sheafify
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Skyscraper
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of module sheafification

This file owns the canonical comparison between the stalk of a module presheaf and the stalk of
its sheafification over a fixed sheaf of commutative rings.  The inverse is defined through the
sheafification and stalk-skyscraper Hom equivalences, rather than extracted from an `IsIso`
instance.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheafification of module presheaves over the fixed commutative-ring sheaf `R`. -/
@[stacks 0D09 "module sheafification functor"]
noncomputable def moduleSheafificationFunctor :
    PresheafOfModules (ringSheafOfComm R).obj ⥤
      SheafOfModules (ringSheafOfComm R) :=
  PresheafOfModules.sheafification (𝟙 (ringSheafOfComm R).obj)

/-- The canonical comparison from the stalk of a module presheaf to the stalk of its
sheafification. -/
@[stacks 0D09 "module sheafification stalk comparison"]
noncomputable def moduleSheafificationStalkComparison
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    PresheafOfModules.stalkModuleCatOfCommRing F x ⟶
      (SheafOfModules.stalkFunctorOfCommRing R x).obj
        ((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm R).obj)).obj F) :=
  PresheafOfModules.stalkMapOfCommRing
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheafOfComm R).obj)).unit.app F) x

/-- The morphism from the sheafification of `F` to the skyscraper sheaf of `Fₓ` extending the
canonical germ map `F ⟶ skyscraper(Fₓ)`. -/
@[stacks 0D09 "sheafification map to the stalk skyscraper"]
noncomputable def moduleSheafificationToSkyscraper
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    (PresheafOfModules.sheafification
        (𝟙 (ringSheafOfComm R).obj)).obj F ⟶
      PresheafOfModules.Skyscraper.sheafAtPoint R x
        (PresheafOfModules.stalkModuleCatOfCommRing F x) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheafOfComm R).obj)).homEquiv F
        (PresheafOfModules.Skyscraper.sheafAtPoint R x
          (PresheafOfModules.stalkModuleCatOfCommRing F x))).symm
    (PresheafOfModules.Skyscraper.toHom R.presheaf x
      (𝟙 (PresheafOfModules.stalkModuleCatOfCommRing F x)))

/-- The explicit inverse from the stalk of the sheafification of `F` to the stalk of `F`. -/
@[stacks 0D09 "inverse module sheafification stalk comparison"]
noncomputable def moduleSheafificationStalkComparisonInv
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    (SheafOfModules.stalkFunctorOfCommRing R x).obj
        ((PresheafOfModules.sheafification
          (𝟙 (ringSheafOfComm R).obj)).obj F) ⟶
      PresheafOfModules.stalkModuleCatOfCommRing F x :=
  (PresheafOfModules.Skyscraper.sheafHomEquiv R x
    ((PresheafOfModules.sheafification
      (𝟙 (ringSheafOfComm R).obj)).obj F)
    (PresheafOfModules.stalkModuleCatOfCommRing F x)).symm
      (moduleSheafificationToSkyscraper R F x)

/-- The map to the stalk skyscraper extends the canonical germ map from `F`. -/
@[stacks 0D09 "module sheafification-to-skyscraper unit law"]
theorem moduleSheafificationToSkyscraper_unit
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheafOfComm R).obj)).unit.app F) ≫
        (moduleSheafificationToSkyscraper R F x).val =
      PresheafOfModules.Skyscraper.toHom R.presheaf x
        (𝟙 (PresheafOfModules.stalkModuleCatOfCommRing F x)) := sorry

/-- The module-sheafification stalk comparison sends a section germ to the germ of its image
under the sheafification unit. -/
@[stacks 0D09 "module sheafification stalk comparison on germs"]
theorem moduleSheafificationStalkComparison_germ
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : F.obj (Opposite.op U)) :
    moduleSheafificationStalkComparison R F x
        (TopCat.Presheaf.germ F.presheaf U x hx m) =
      TopCat.Presheaf.germ
        ((PresheafOfModules.sheafification
          (𝟙 (ringSheafOfComm R).obj)).obj F).val.presheaf U x hx
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheafOfComm R).obj)).unit.app F).app (Opposite.op U) m) := sorry

/-- The inverse sheafification-stalk comparison sends the germ of the sheafification image of a
section back to its original germ. -/
@[stacks 0D09 "inverse module sheafification stalk comparison on germs"]
theorem moduleSheafificationStalkComparisonInv_germ
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : F.obj (Opposite.op U)) :
    moduleSheafificationStalkComparisonInv R F x
        (TopCat.Presheaf.germ
          ((PresheafOfModules.sheafification
            (𝟙 (ringSheafOfComm R).obj)).obj F).val.presheaf U x hx
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheafOfComm R).obj)).unit.app F).app (Opposite.op U) m)) =
      TopCat.Presheaf.germ F.presheaf U x hx m := sorry

/-- The sheafification-stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 0D09 "module sheafification stalk forward-inverse law"]
theorem moduleSheafificationStalkComparison_hom_inv_id
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    moduleSheafificationStalkComparison R F x ≫
      moduleSheafificationStalkComparisonInv R F x = 𝟙 _ := sorry

/-- The explicit inverse followed by the sheafification-stalk comparison is the identity. -/
@[simp, stacks 0D09 "module sheafification stalk inverse-forward law"]
theorem moduleSheafificationStalkComparison_inv_hom_id
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    moduleSheafificationStalkComparisonInv R F x ≫
      moduleSheafificationStalkComparison R F x = 𝟙 _ := sorry

/-- The canonical isomorphism from the stalk of a module presheaf to the stalk of its
sheafification, with both morphisms explicitly owned by this API. -/
@[stacks 0D09 "module sheafification stalk isomorphism"]
noncomputable def moduleSheafificationStalkIso
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    PresheafOfModules.stalkModuleCatOfCommRing F x ≅
      (SheafOfModules.stalkFunctorOfCommRing R x).obj
        ((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm R).obj)).obj F) where
  hom := moduleSheafificationStalkComparison R F x
  inv := moduleSheafificationStalkComparisonInv R F x
  hom_inv_id := moduleSheafificationStalkComparison_hom_inv_id R F x
  inv_hom_id := moduleSheafificationStalkComparison_inv_hom_id R F x

/-- The forward morphism of the module-sheafification stalk isomorphism is the canonical
comparison. -/
@[simp, stacks 0D09 "module sheafification stalk isomorphism hom"]
theorem moduleSheafificationStalkIso_hom
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    (moduleSheafificationStalkIso R F x).hom =
      moduleSheafificationStalkComparison R F x := sorry

/-- The inverse morphism of the module-sheafification stalk isomorphism is the explicit inverse
comparison. -/
@[simp, stacks 0D09 "module sheafification stalk isomorphism inverse"]
theorem moduleSheafificationStalkIso_inv
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    (moduleSheafificationStalkIso R F x).inv =
      moduleSheafificationStalkComparisonInv R F x := sorry

/-- The sheafification-stalk comparison is natural in the module presheaf. -/
@[stacks 0D09 "module sheafification stalk comparison naturality"]
theorem moduleSheafificationStalkComparison_naturality
    {F G : PresheafOfModules (ringSheafOfComm R).obj} (f : F ⟶ G) (x : X) :
    PresheafOfModules.stalkMapOfCommRing f x ≫
        moduleSheafificationStalkComparison R G x =
      moduleSheafificationStalkComparison R F x ≫
        (SheafOfModules.stalkFunctorOfCommRing R x).map
          ((PresheafOfModules.sheafification
            (𝟙 (ringSheafOfComm R).obj)).map f) := sorry

/-- The inverse sheafification-stalk comparison is natural in the module presheaf. -/
@[stacks 0D09 "inverse module sheafification stalk comparison naturality"]
theorem moduleSheafificationStalkComparisonInv_naturality
    {F G : PresheafOfModules (ringSheafOfComm R).obj} (f : F ⟶ G) (x : X) :
    (SheafOfModules.stalkFunctorOfCommRing R x).map
          ((PresheafOfModules.sheafification
            (𝟙 (ringSheafOfComm R).obj)).map f) ≫
        moduleSheafificationStalkComparisonInv R G x =
        moduleSheafificationStalkComparisonInv R F x ≫
        PresheafOfModules.stalkMapOfCommRing f x := sorry

/-- The forward natural transformation from module-presheaf stalks to sheafified module stalks. -/
@[stacks 0D09 "module sheafification stalk natural comparison"]
noncomputable def moduleSheafificationStalkNatTrans (x : X) :
    PresheafOfModules.stalkFunctorOfCommRing R.presheaf x ⟶
      moduleSheafificationFunctor R ⋙
        SheafOfModules.stalkFunctorOfCommRing R x where
  app F := moduleSheafificationStalkComparison R F x
  naturality _ _ f := moduleSheafificationStalkComparison_naturality R f x

/-- The inverse natural transformation from sheafified module stalks to module-presheaf stalks. -/
@[stacks 0D09 "inverse module sheafification stalk natural comparison"]
noncomputable def moduleSheafificationStalkInvNatTrans (x : X) :
    moduleSheafificationFunctor R ⋙
        SheafOfModules.stalkFunctorOfCommRing R x ⟶
      PresheafOfModules.stalkFunctorOfCommRing R.presheaf x where
  app F := moduleSheafificationStalkComparisonInv R F x
  naturality _ _ f := moduleSheafificationStalkComparisonInv_naturality R f x

/-- The forward and inverse module-sheafification stalk transformations compose to the identity. -/
@[simp, stacks 0D09 "module sheafification stalk natural forward-inverse law"]
theorem moduleSheafificationStalkNatTrans_hom_inv_id (x : X) :
    moduleSheafificationStalkNatTrans R x ≫
      moduleSheafificationStalkInvNatTrans R x = 𝟙 _ := sorry

/-- The inverse and forward module-sheafification stalk transformations compose to the identity. -/
@[simp, stacks 0D09 "module sheafification stalk natural inverse-forward law"]
theorem moduleSheafificationStalkNatTrans_inv_hom_id (x : X) :
    moduleSheafificationStalkInvNatTrans R x ≫
      moduleSheafificationStalkNatTrans R x = 𝟙 _ := sorry

/-- The natural isomorphism between module-presheaf stalks and sheafified module stalks. -/
@[stacks 0D09 "module sheafification stalk natural isomorphism"]
noncomputable def moduleSheafificationStalkNatIso (x : X) :
    PresheafOfModules.stalkFunctorOfCommRing R.presheaf x ≅
      moduleSheafificationFunctor R ⋙
        SheafOfModules.stalkFunctorOfCommRing R x where
  hom := moduleSheafificationStalkNatTrans R x
  inv := moduleSheafificationStalkInvNatTrans R x
  hom_inv_id := moduleSheafificationStalkNatTrans_hom_inv_id R x
  inv_hom_id := moduleSheafificationStalkNatTrans_inv_hom_id R x

/-- The component of the module-sheafification stalk natural isomorphism is the objectwise
   stalk isomorphism. -/
@[simp, stacks 0D09 "module sheafification stalk natural isomorphism component"]
theorem moduleSheafificationStalkNatIso_app
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    (moduleSheafificationStalkNatIso R x).app F =
      moduleSheafificationStalkIso R F x := sorry

/-- The forward natural transformation of the module-sheafification stalk natural isomorphism. -/
@[simp, stacks 0D09 "module sheafification stalk natural isomorphism hom"]
theorem moduleSheafificationStalkNatIso_hom (x : X) :
    (moduleSheafificationStalkNatIso R x).hom =
      moduleSheafificationStalkNatTrans R x := sorry

/-- The inverse natural transformation of the module-sheafification stalk natural isomorphism. -/
@[simp, stacks 0D09 "module sheafification stalk natural isomorphism inverse"]
theorem moduleSheafificationStalkNatIso_inv (x : X) :
    (moduleSheafificationStalkNatIso R x).inv =
      moduleSheafificationStalkInvNatTrans R x := sorry

/-- Components of the forward natural isomorphism are the canonical stalk comparisons. -/
@[simp, stacks 0D09 "module sheafification stalk natural isomorphism hom component"]
theorem moduleSheafificationStalkNatIso_hom_app
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    (moduleSheafificationStalkNatIso R x).hom.app F =
      moduleSheafificationStalkComparison R F x := sorry

/-- Components of the inverse natural isomorphism are the explicit inverse stalk comparisons. -/
@[simp, stacks 0D09 "module sheafification stalk natural isomorphism inverse component"]
theorem moduleSheafificationStalkNatIso_inv_app
    (F : PresheafOfModules (ringSheafOfComm R).obj) (x : X) :
    (moduleSheafificationStalkNatIso R x).inv.app F =
      moduleSheafificationStalkComparisonInv R F x := sorry

end TopCat.Sheaf
