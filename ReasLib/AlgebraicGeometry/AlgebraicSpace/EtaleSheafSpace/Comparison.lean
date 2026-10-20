module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Subcanonical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Localization

/-!
# Comparison isomorphisms for the algebraic space of an étale sheaf

The sheaf `F` on `Y_étale` is identified with the representable sheaf of
`sheafSpace F h` on `Y_spaces,étale`, and with the extension by zero of the
terminal sheaf along `sheafSpaceTo F h`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Y : AlgebraicSpace S}

/-- Reconstructing an object of the small étale site from its structure morphism. -/
theorem smallEtaleSite.mk_self {X : AlgebraicSpace S} (V : smallEtaleSite X) :
    @smallEtaleSite.mk S X V.left V.hom V.prop = V :=
  sorry

/-- Transport of sections of `F` along `smallEtaleSite.mk_self`. -/
def etaleSheaf_mkSelfIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (V : smallEtaleSite X) :
    F.obj.obj (op (@smallEtaleSite.mk S X V.left V.hom V.prop)) ≅ F.obj.obj (op V) :=
  eqToIso (congrArg (fun W ↦ F.obj.obj (op W)) (smallEtaleSite.mk_self V))

/-- A section of `F` over `V` as a global section of `V.hom_small⁻¹ F`. -/
def etaleInverseImageSections.ofObj (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (V : smallEtaleSite Y) (s : F.obj.obj (op V)) :
    etaleInverseImageSections V.hom F :=
  (@smallEtaleMorphismOfTopoi_inverseImage_obj S (ofOver V.left) Y V.hom V.prop F
      (smallEtaleSite.id V.left)).inv
    ((etaleSheaf_mkSelfIso F V).inv s)

/-- A global section of `V.hom_small⁻¹ F` as a section of `F` over `V`. -/
def etaleInverseImageSections.toObj (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (V : smallEtaleSite Y) (s : etaleInverseImageSections V.hom F) :
    F.obj.obj (op V) :=
  (etaleSheaf_mkSelfIso F V).hom
    ((@smallEtaleMorphismOfTopoi_inverseImage_obj S (ofOver V.left) Y V.hom V.prop F
        (smallEtaleSite.id V.left)).hom s)

/-- The object of `Y_spaces,étale` determined by `sheafSpaceTo F h`. -/
abbrev sheafSpaceTo.spacesEtale (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : spacesEtaleSite Y :=
  spacesEtaleSite.mk (sheafSpaceTo F h)

/-- The representable sheaf `h_X` on `Y_spaces,étale` associated to `sheafSpace F h`. -/
abbrev sheafSpace_yoneda (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : Sheaf (spacesEtaleTopology Y) (Type (u + 1)) :=
  (spacesEtaleTopology Y).yoneda.obj (sheafSpaceTo.spacesEtale F h)

/-- Restriction of `h_X` along `smallEtaleToSpaces Y`. -/
abbrev sheafSpace_yonedaRestrict (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : Sheaf (smallEtaleTopology Y) (Type (u + 1)) :=
  ((smallEtaleToSpaces Y).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology Y) (spacesEtaleTopology Y)).obj
    (sheafSpace_yoneda F h)

/-- The morphism over `Y` associated to a section of `F` on a scheme étale over `Y`. -/
def sheafSpace_homOfSection (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y) (s : F.obj.obj (op V)) :
    (smallEtaleToSpaces Y).obj V ⟶ sheafSpaceTo.spacesEtale F h :=
  Over.homMk (sheafSpace.homOfPair F h ⟨V.hom, etaleInverseImageSections.ofObj F V s⟩) sorry

/-- The pair associated to a morphism over `Y` into `sheafSpace F h`. -/
def sheafSpace_pairOfHom (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y)
    (φ : (smallEtaleToSpaces Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) :
    sheafSpacePair F V.left :=
  (@equivShrink.{u} (sheafSpacePair F V.left) (h V.left)).symm (yonedaEquiv φ.left)

/-- The morphism to `Y` extracted from `sheafSpace_pairOfHom` is the structure morphism of
`V`. -/
theorem sheafSpace_pairOfHom_fst (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y)
    (φ : (smallEtaleToSpaces Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) :
    (sheafSpace_pairOfHom F h V φ).1 = V.hom :=
  sorry

/-- The section of `F` associated to a morphism over `Y` into `sheafSpace F h`. -/
def sheafSpace_sectionOfHom (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y)
    (φ : (smallEtaleToSpaces Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) :
    F.obj.obj (op V) :=
  etaleInverseImageSections.toObj F V
    (eqToHom (congrArg (fun y ↦ etaleInverseImageSections y F)
      (sheafSpace_pairOfHom_fst F h V φ)) (sheafSpace_pairOfHom F h V φ).2)

/-- On the small étale site, `F` is isomorphic to the restriction of `h_X`. -/
def sheafSpace_smallIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : F ≅ sheafSpace_yonedaRestrict F h := by
  refine
    { hom := ⟨{ app := fun V ↦ TypeCat.ofHom fun s ↦ sheafSpace_homOfSection F h V.unop s
                naturality := ?_ }⟩
      inv := ⟨{ app := fun V ↦ TypeCat.ofHom fun φ ↦ sheafSpace_sectionOfHom F h V.unop φ
                naturality := ?_ }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals sorry

/-- Via `Sh(Y_étale) = Sh(Y_spaces,étale)`, the sheaf `F` is isomorphic to the
representable sheaf of `sheafSpace F h`. -/
def sheafSpace_yonedaIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    (smallEtaleInclusionDirectImage Y).obj F ≅ sheafSpace_yoneda F h :=
  (smallEtaleInclusionDirectImage Y).mapIso
      (sheafSpace_smallIso F h ≪≫
        (smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous Y).symm.app
          (sheafSpace_yoneda F h)) ≪≫
    (smallEtalePresentationEquivalence Y).counitIso.app (sheafSpace_yoneda F h)

/-- `sheafSpace_yonedaIso` is the transport of `sheafSpace_smallIso` along the comparison
equivalence of the small and spaces étale sites. -/
theorem sheafSpace_yonedaIso_spec (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_yonedaIso F h =
      (smallEtaleInclusionDirectImage Y).mapIso
          (sheafSpace_smallIso F h ≪≫
            (smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous Y).symm.app
              (sheafSpace_yoneda F h)) ≪≫
        (smallEtalePresentationEquivalence Y).counitIso.app
          (sheafSpace_yoneda F h) :=
  rfl

/-- The extension-by-zero formula for the terminal sheaf: on `V` this is the coproduct of a point
indexed by morphisms `V ⟶ X` over `Y`. -/
def sheafSpace_shriekFormula (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : (smallEtaleSite Y)ᵒᵖ ⥤ Type (u + 1) := by
  refine
    { obj V :=
        ((smallEtaleToSpaces Y).obj V.unop ⟶ sheafSpaceTo.spacesEtale F h) × PUnit.{u + 1}
      map {V W} f :=
        TypeCat.ofHom fun p ↦ ⟨(smallEtaleToSpaces Y).map f.unop ≫ p.1, p.2⟩
      map_id := ?_
      map_comp := ?_ }
  all_goals sorry

/-- Values of `sheafSpace_shriekFormula` are pairs consisting of a morphism over `Y` into
`sheafSpace F h` and a point. -/
theorem sheafSpace_shriekFormula_obj (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y) :
    (sheafSpace_shriekFormula F h).obj (op V) =
      (((smallEtaleToSpaces Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) × PUnit.{u + 1}) :=
  rfl

/-- Sheafification of the extension-by-zero formula for the terminal sheaf. -/
def sheafSpace_shriekTerminal (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : Sheaf (smallEtaleTopology Y) (Type (u + 1)) :=
  (presheafToSheaf (smallEtaleTopology Y) (Type (u + 1))).obj (sheafSpace_shriekFormula F h)

/-- `sheafSpace_shriekTerminal` is the sheafification of `sheafSpace_shriekFormula`. -/
theorem sheafSpace_shriekTerminal_eq (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_shriekTerminal F h =
      (presheafToSheaf (smallEtaleTopology Y) (Type (u + 1))).obj
        (sheafSpace_shriekFormula F h) :=
  rfl

/-- The extension-by-zero formula for the terminal sheaf is the restricted representable presheaf `h_X`. -/
def sheafSpace_shriekFormulaIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_shriekFormula F h ≅
      (sheafToPresheaf (smallEtaleTopology Y) (Type (u + 1))).obj
        (sheafSpace_yonedaRestrict F h) := by
  refine
    { hom :=
        { app := fun V ↦ TypeCat.ofHom fun p ↦ p.1
          naturality := ?_ }
      inv :=
        { app := fun V ↦ TypeCat.ofHom fun φ ↦ ⟨φ, ⟨⟩⟩
          naturality := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals sorry

/-- Identification of the sheafified extension-by-zero formula with the restriction of `h_X`. -/
def sheafSpace_shriekIso_restrict (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_shriekTerminal F h ≅ sheafSpace_yonedaRestrict F h :=
  (presheafToSheaf (smallEtaleTopology Y) (Type (u + 1))).mapIso
      (sheafSpace_shriekFormulaIso F h) ≪≫
    (sheafificationIso (sheafSpace_yonedaRestrict F h)).symm

/-- `F` is isomorphic to the extension by zero of the terminal sheaf along `sheafSpaceTo F h`,
constructed as the sheafification of the extension-by-zero formula for the terminal sheaf. -/
def sheafSpace_shriekIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : F ≅ sheafSpace_shriekTerminal F h :=
  sheafSpace_smallIso F h ≪≫ (sheafSpace_shriekIso_restrict F h).symm

/-- `sheafSpace_shriekIso` is `sheafSpace_smallIso` composed with the formula comparison. -/
theorem sheafSpace_shriekIso_spec (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_shriekIso F h =
      sheafSpace_smallIso F h ≪≫ (sheafSpace_shriekIso_restrict F h).symm :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
