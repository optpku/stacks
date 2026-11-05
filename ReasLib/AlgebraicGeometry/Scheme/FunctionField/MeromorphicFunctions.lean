/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Meromorphic
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Rational functions as global meromorphic functions

On an integral scheme, rational functions determine global meromorphic sections through
comparison with the meromorphic stalk at the generic point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The canonical stalk map `K(X) ⟶ 𝒦_{X, η}` induced by `𝒪_X ⟶ 𝒦_X` at the generic
point. -/
def functionFieldToMeromorphicStalk :
    X.functionField ⟶
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X) :=
  (TopCat.Presheaf.stalkFunctor CommRingCat (genericPoint X)).map
    X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom

/-- The germ map `Γ(X, 𝒦_X) ⟶ 𝒦_{X, η}` on global meromorphic functions. -/
def meromorphicGermGenericPoint :
    X.toLocallyRingedSpace.meromorphicFunctions ⟶
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X) :=
  X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.germ ⊤ (genericPoint X) trivial

/-- On an integral scheme the generic germ of global meromorphic functions is bijective.
The constant-sheaf comparison identifies it with the generic germ of a skyscraper sheaf. -/
theorem meromorphicGermGenericPoint_bijective :
    Function.Bijective (meromorphicGermGenericPoint X).hom := by
  classical
  let η := genericPoint X
  let A := X.functionField
  let P : X.toTopCat.Presheaf CommRingCat :=
    (Functor.const (TopologicalSpace.Opens X.toTopCat)ᵒᵖ).obj A
  let Q := (constantSheaf (Opens.grothendieckTopology X.toTopCat)
    CommRingCat).obj A
  let G := TopCat.Sheaf.Skyscraper.atPoint η A
  have hP (x : X) : IsIso (P.Γgerm x) := by
    let c : Cocone ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ P) :=
      Cocone.mk A
        { app := fun _ ↦ 𝟙 A
          naturality := fun _ _ _ ↦ by
            change 𝟙 A ≫ 𝟙 A = 𝟙 A ≫ 𝟙 A
            simp }
    let q : P.stalk x ⟶ A := colimit.desc _ c
    let e : P.stalk x ≅ A :=
      { hom := q
        inv := P.Γgerm x
        hom_inv_id := by
          apply TopCat.Presheaf.stalk_hom_ext P
          intro U hxU
          erw [← Category.assoc]
          dsimp only [q, TopCat.Presheaf.germ]
          erw [colimit.ι_desc]
          dsimp only [c]
          erw [Category.id_comp, Category.comp_id]
          have h := (P.map_germ_eq_Γgerm
            (i := CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)) x hxU).symm
          erw [Category.id_comp] at h
          exact eq_of_heq (heq_of_eq h)
        inv_hom_id := by
          change P.Γgerm x ≫ q = 𝟙 A
          dsimp only [TopCat.Presheaf.Γgerm, q]
          erw [colimit.ι_desc] }
    exact e.isIso_inv
  have hG (x : X) : IsIso (G.presheaf.Γgerm x) := by
    let h : Specializes η x := (genericPoint_spec X).specializes trivial
    let e := TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes η A h
    have he : G.presheaf.Γgerm x ≫ e.hom =
        (eqToIso (show G.presheaf.obj (op ⊤) = A from if_pos trivial)).hom :=
      germ_skyscraperPresheafStalkOfSpecializes_hom η A h ⊤ trivial
    haveI : IsIso (G.presheaf.Γgerm x ≫ e.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ e.hom
  let c : P ⟶ G.presheaf :=
    { app := fun U ↦
        if h : η ∈ U.unop then eqToHom (if_pos h).symm
        else ((if_neg h).symm.ndrec terminalIsTerminal).from A
      naturality := by
        intro U V i
        by_cases hV : η ∈ V.unop
        · have hU : η ∈ U.unop := i.unop.le hV
          simp [P, G, TopCat.Sheaf.Skyscraper.atPoint, skyscraperSheaf,
            skyscraperPresheaf, hV, hU]
        · dsimp [G, TopCat.Sheaf.Skyscraper.atPoint, skyscraperSheaf]
          apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext }
  have hcTop : IsIso (c.app (op ⊤)) := by
    dsimp only [c]
    rw [dif_pos (show η ∈ (⊤ : TopologicalSpace.Opens X.toTopCat) from trivial)]
    infer_instance
  have hc (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map c) := by
    letI := hP x
    letI := hG x
    letI := hcTop
    have hn := TopCat.Presheaf.stalkFunctor_map_germ ⊤ x trivial c
    haveI : IsIso (P.Γgerm x ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map c) := by
      erw [hn]
      exact IsIso.comp_isIso' hcTop (hG x)
    exact IsIso.of_isIso_comp_left (P.Γgerm x) _
  let d : Q ⟶ G := Sheaf.homEquiv.symm <|
    sheafifyLift (Opens.grothendieckTopology X.toTopCat) c G.property
  have hd (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map d.hom) := by
    let a := toSheafify (Opens.grothendieckTopology X.toTopCat) P
    have ha : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map a) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat P
    letI := ha
    have hfac : a ≫ d.hom = c := toSheafify_sheafifyLift _ _ _
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map a ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat x).map d.hom) := by
      rw [← Functor.map_comp, hfac]
      exact hc x
    exact IsIso.of_isIso_comp_left
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map a) _
  letI (x : X.toTopCat) :
      IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map d.hom) := hd x
  letI : IsIso d := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso d
  obtain ⟨eF⟩ := meromorphicFunctionSheaf_isIsomorphic_constantFunctionField (X := X)
  let e := eF ≪≫ asIso d
  let eP := (TopCat.Sheaf.forget CommRingCat X.toTopCat).mapIso e
  letI : IsIso (e.hom.hom.app (op ⊤)) := (eP.app (op ⊤)).isIso_hom
  letI : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat η).map e.hom.hom) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat η).mapIso eP).isIso_hom
  letI := hG η
  have hn := TopCat.Presheaf.stalkFunctor_map_germ ⊤ η trivial e.hom.hom
  haveI : IsIso (X.meromorphicFunctionSheaf.presheaf.Γgerm η ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat η).map e.hom.hom) := by
    erw [hn]
    exact IsIso.comp_isIso' (eP.app (op ⊤)).isIso_hom (hG η)
  haveI : IsIso (X.meromorphicFunctionSheaf.presheaf.Γgerm η) :=
    IsIso.of_isIso_comp_right _
      ((TopCat.Presheaf.stalkFunctor CommRingCat η).map e.hom.hom)
  exact ConcreteCategory.bijective_of_isIso (X.meromorphicFunctionSheaf.presheaf.Γgerm η)

/-- The canonical comparison `K(X) ⟶ Γ(X, 𝒦_X)`, sending a rational function to the unique
global meromorphic section whose germ at the generic point is its image in `𝒦_{X, η}`. -/
def functionFieldToMeromorphicFunctions :
    X.functionField ⟶ X.toLocallyRingedSpace.meromorphicFunctions :=
  functionFieldToMeromorphicStalk X ≫
    CommRingCat.ofHom
      { toFun := Function.invFun (meromorphicGermGenericPoint X).hom
        map_one' := by
          apply (meromorphicGermGenericPoint_bijective X).injective
          rw [Function.rightInverse_invFun
            (meromorphicGermGenericPoint_bijective X).surjective, map_one]
        map_mul' := by
          intro a b
          apply (meromorphicGermGenericPoint_bijective X).injective
          exact (Function.rightInverse_invFun
            (meromorphicGermGenericPoint_bijective X).surjective (a * b)).trans
              (((meromorphicGermGenericPoint X).hom.map_mul _ _).trans
                (congrArg₂ (· * ·)
                  (Function.rightInverse_invFun
                    (meromorphicGermGenericPoint_bijective X).surjective a)
                  (Function.rightInverse_invFun
                    (meromorphicGermGenericPoint_bijective X).surjective b))).symm
        map_zero' := by
          apply (meromorphicGermGenericPoint_bijective X).injective
          rw [Function.rightInverse_invFun
            (meromorphicGermGenericPoint_bijective X).surjective, map_zero]
        map_add' := by
          intro a b
          apply (meromorphicGermGenericPoint_bijective X).injective
          exact (Function.rightInverse_invFun
            (meromorphicGermGenericPoint_bijective X).surjective (a + b)).trans
              (((meromorphicGermGenericPoint X).hom.map_add _ _).trans
                (congrArg₂ (· + ·)
                  (Function.rightInverse_invFun
                    (meromorphicGermGenericPoint_bijective X).surjective a)
                  (Function.rightInverse_invFun
                    (meromorphicGermGenericPoint_bijective X).surjective b))).symm }

/-- The germ at the generic point of the meromorphic image of a rational function is the
canonical stalk map. -/
theorem functionFieldToMeromorphicFunctions_germ (f : X.functionField) :
    meromorphicGermGenericPoint X (functionFieldToMeromorphicFunctions X f) =
      functionFieldToMeromorphicStalk X f := by
  exact Function.rightInverse_invFun
    (meromorphicGermGenericPoint_bijective X).surjective _

/-- A global meromorphic function with the prescribed generic germ is the canonical image. -/
theorem functionFieldToMeromorphicFunctions_unique (f : X.functionField)
    (s : X.toLocallyRingedSpace.meromorphicFunctions)
    (hs : meromorphicGermGenericPoint X s = functionFieldToMeromorphicStalk X f) :
    s = functionFieldToMeromorphicFunctions X f :=
  (meromorphicGermGenericPoint_bijective X).injective
    (hs.trans (functionFieldToMeromorphicFunctions_germ X f).symm)

/-- The global meromorphic unit associated to a rational function. -/
def meromorphicUnitOfFunctionField (f : X.functionFieldˣ) :
    (X.toLocallyRingedSpace.meromorphicFunctions)ˣ :=
  Units.map (functionFieldToMeromorphicFunctions X).hom.toMonoidHom f

end AlgebraicGeometry.Scheme
