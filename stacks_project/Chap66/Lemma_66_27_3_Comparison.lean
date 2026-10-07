module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap66.«66_27_0_1_Comparison»
public import stacks_project.Chap66.Lemma_66_18_11
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap66.Lemma_66_27_3_Space

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

/-- Restriction of `h_X` along `smallEtaleInclusion Y`. -/
abbrev sheafSpace_yonedaRestrict (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : Sheaf (smallEtaleTopology Y) (Type (u + 1)) :=
  ((smallEtaleInclusion Y).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology Y) (spacesEtaleTopology Y)).obj
    (sheafSpace_yoneda F h)

/-- The morphism over `Y` associated to a section of `F` on a scheme étale over `Y`. -/
def sheafSpace_homOfSection (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y) (s : F.obj.obj (op V)) :
    (smallEtaleInclusion Y).obj V ⟶ sheafSpaceTo.spacesEtale F h :=
  Over.homMk (sheafSpace.homOfPair F h ⟨V.hom, etaleInverseImageSections.ofObj F V s⟩) sorry

/-- The pair associated to a morphism over `Y` into `sheafSpace F h`. -/
def sheafSpace_pairOfHom (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y)
    (φ : (smallEtaleInclusion Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) :
    sheafSpacePair F V.left :=
  (@equivShrink.{u} (sheafSpacePair F V.left) (h V.left)).symm (yonedaEquiv φ.left)

/-- The morphism to `Y` extracted from `sheafSpace_pairOfHom` is the structure morphism of
`V`. -/
theorem sheafSpace_pairOfHom_fst (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y)
    (φ : (smallEtaleInclusion Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) :
    (sheafSpace_pairOfHom F h V φ).1 = V.hom :=
  sorry

/-- The section of `F` associated to a morphism over `Y` into `sheafSpace F h`. -/
def sheafSpace_sectionOfHom (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y)
    (φ : (smallEtaleInclusion Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) :
    F.obj.obj (op V) :=
  etaleInverseImageSections.toObj F V
    (eqToHom (congrArg (fun y ↦ etaleInverseImageSections y F)
      (sheafSpace_pairOfHom_fst F h V φ)) (sheafSpace_pairOfHom F h V φ).2)

/-- On the small étale site, `F` is isomorphic to the restriction of `h_X`. -/
def sheafSpace_smallIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : F ≅ sheafSpace_yonedaRestrict F h where
  hom := ⟨{ app := fun V ↦ TypeCat.ofHom fun s ↦ sheafSpace_homOfSection F h V.unop s
            naturality := sorry }⟩
  inv := ⟨{ app := fun V ↦ TypeCat.ofHom fun φ ↦ sheafSpace_sectionOfHom F h V.unop φ
            naturality := sorry }⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Via `Sh(Y_étale) = Sh(Y_spaces,étale)`, the sheaf `F` is isomorphic to the
representable sheaf of `sheafSpace F h`. -/
def sheafSpace_yonedaIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    (smallEtaleInclusionDirectImage Y).obj F ≅ sheafSpace_yoneda F h :=
  (smallEtaleInclusionDirectImage Y).mapIso
      (sheafSpace_smallIso F h ≪≫
        (smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous Y).symm.app
          (sheafSpace_yoneda F h)) ≪≫
    (smallEtaleInclusionDirectImage Y).asEquivalence.counitIso.app (sheafSpace_yoneda F h)

/-- `sheafSpace_yonedaIso` is the transport of `sheafSpace_smallIso` along the comparison
equivalence of Lemma 66.18.3. -/
theorem sheafSpace_yonedaIso_spec (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_yonedaIso F h =
      (smallEtaleInclusionDirectImage Y).mapIso
          (sheafSpace_smallIso F h ≪≫
            (smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous Y).symm.app
              (sheafSpace_yoneda F h)) ≪≫
        (smallEtaleInclusionDirectImage Y).asEquivalence.counitIso.app
          (sheafSpace_yoneda F h) :=
  rfl

/-- The Sites, Lemma 7.25.3 formula for `j_!(*)`: on `V` this is the coproduct of a point
indexed by morphisms `V ⟶ X` over `Y`. -/
def sheafSpace_shriekFormula (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : (smallEtaleSite Y)ᵒᵖ ⥤ Type (u + 1) where
  obj V :=
    ((smallEtaleInclusion Y).obj V.unop ⟶ sheafSpaceTo.spacesEtale F h) × PUnit.{u + 1}
  map {V W} f :=
    TypeCat.ofHom fun p ↦ ⟨(smallEtaleInclusion Y).map f.unop ≫ p.1, p.2⟩
  map_id := sorry
  map_comp := sorry

/-- Values of `sheafSpace_shriekFormula` are pairs consisting of a morphism over `Y` into
`sheafSpace F h` and a point. -/
theorem sheafSpace_shriekFormula_obj (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (V : smallEtaleSite Y) :
    (sheafSpace_shriekFormula F h).obj (op V) =
      (((smallEtaleInclusion Y).obj V ⟶ sheafSpaceTo.spacesEtale F h) × PUnit.{u + 1}) :=
  rfl

/-- Sheafification of the Sites, Lemma 7.25.3 formula for `f_small,! *`. -/
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

/-- The structure morphism over `Y` from the postcomposition of `U` with `sheafSpaceTo F h`. -/
def sheafSpace_uniqueOverHom (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (U : smallEtaleSite (sheafSpace F h)) :
    (smallEtaleInclusion Y).obj ((etaleRestriction (sheafSpaceTo F h)).obj U) ⟶
      sheafSpaceTo.spacesEtale F h :=
  Over.homMk U.hom sorry

/-- Inverse image of the restricted representable sheaf along `sheafSpaceTo F h`. -/
abbrev sheafSpace_yonedaRestrictInverseImage
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F) :
    Sheaf (smallEtaleTopology (sheafSpace F h)) (Type (u + 1)) :=
  ((etaleRestriction (sheafSpaceTo F h)).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology (sheafSpace F h)) (smallEtaleTopology Y)).obj
    (sheafSpace_yonedaRestrict F h)

/-- The structure-section family of morphisms over `Y` from an arbitrary sheaf on `X_étale`
into `f⁻¹ h_X`. -/
def sheafSpace_yonedaRestrictInverseImage_from
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F)
    (G : Sheaf (smallEtaleTopology (sheafSpace F h)) (Type (u + 1))) :
    G ⟶ sheafSpace_yonedaRestrictInverseImage F h :=
  ⟨{ app := fun U ↦ TypeCat.ofHom fun _ ↦ sheafSpace_uniqueOverHom F h U.unop
     naturality := sorry }⟩

/-- The map `* ⟶ f⁻¹ h_X` obtained by applying the structure-section family to the terminal
sheaf on `X_étale`. -/
def sheafSpace_terminalToYonedaRestrictInverseImage
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F) :
    Sheaf.terminal (smallEtaleTopology (sheafSpace F h)) Types.isTerminalPUnit ⟶
      sheafSpace_yonedaRestrictInverseImage F h :=
  sheafSpace_yonedaRestrictInverseImage_from F h
    (Sheaf.terminal (smallEtaleTopology (sheafSpace F h)) Types.isTerminalPUnit)

/-- `sheafSpace_terminalToYonedaRestrictInverseImage` is the structure-section family on the
terminal sheaf. -/
theorem sheafSpace_terminalToYonedaRestrictInverseImage_eq
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F) :
    sheafSpace_terminalToYonedaRestrictInverseImage F h =
      sheafSpace_yonedaRestrictInverseImage_from F h
        (Sheaf.terminal (smallEtaleTopology (sheafSpace F h)) Types.isTerminalPUnit) :=
  rfl

/-- The Sites, Lemma 7.25.3 formula for `j_!(*)` is the restricted representable sheaf `h_X`. -/
def sheafSpace_shriekFormulaIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_shriekFormula F h ≅
      (sheafToPresheaf (smallEtaleTopology Y) (Type (u + 1))).obj
        (sheafSpace_yonedaRestrict F h) where
  hom :=
    { app := fun V ↦ TypeCat.ofHom fun p ↦ p.1
      naturality := sorry }
  inv :=
    { app := fun V ↦ TypeCat.ofHom fun φ ↦ ⟨φ, ⟨⟩⟩
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification of the sheafified Sites, Lemma 7.25.3 formula with the restriction of `h_X`. -/
def sheafSpace_shriekIso_restrict (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_shriekTerminal F h ≅ sheafSpace_yonedaRestrict F h :=
  (presheafToSheaf (smallEtaleTopology Y) (Type (u + 1))).mapIso
      (sheafSpace_shriekFormulaIso F h) ≪≫
    (sheafificationIso (sheafSpace_yonedaRestrict F h)).symm

/-- `F` is isomorphic to the extension by zero of the terminal sheaf along `sheafSpaceTo F h`,
constructed as the sheafification of the Sites, Lemma 7.25.3 formula for `j_!(*)`. -/
def sheafSpace_shriekIso (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : F ≅ sheafSpace_shriekTerminal F h :=
  sheafSpace_smallIso F h ≪≫ (sheafSpace_shriekIso_restrict F h).symm

/-- `sheafSpace_shriekIso` is `sheafSpace_smallIso` composed with the formula comparison. -/
theorem sheafSpace_shriekIso_spec (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    sheafSpace_shriekIso F h =
      sheafSpace_smallIso F h ≪≫ (sheafSpace_shriekIso_restrict F h).symm :=
  rfl

/-- If continuous sheaf pushforward along `etaleRestriction` is a right adjoint, the Sites,
Lemma 7.25.3 formula for `f_small,! *` is isomorphic to sheaf pullback of the terminal sheaf. -/
theorem sheafSpace_shriekTerminal_sheafPullback
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F)
    [((etaleRestriction (sheafSpaceTo F h)).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology (sheafSpace F h)) (smallEtaleTopology Y)).IsRightAdjoint] :
    Nonempty
      (sheafSpace_shriekTerminal F h ≅
        ((etaleRestriction (sheafSpaceTo F h)).sheafPullback (Type (u + 1))
            (smallEtaleTopology (sheafSpace F h)) (smallEtaleTopology Y)).obj
          (Sheaf.terminal (smallEtaleTopology (sheafSpace F h)) Types.isTerminalPUnit)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
