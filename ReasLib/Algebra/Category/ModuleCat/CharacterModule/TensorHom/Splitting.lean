/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EpiMono
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

universe u

namespace CharacterModule.TensorHom

variable (R : Type u) [CommRing R]

/-- Character duals of tensor products, curried with the right tensor factor first. -/
@[reducible]
def rightFunctor :
    (ModuleCat.{u} R)ᵒᵖ ⥤ (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (Functor.curry.obj
    ((prodOpEquiv (ModuleCat.{u} R)).inverse ⋙ tensorFunctor R)).flip

/-- Evaluating `rightFunctor R` at `Mᵒᵖ` and `Pᵒᵖ` gives the character module of
`P ⊗ M`. -/
theorem rightFunctor_obj (M P : ModuleCat.{u} R) :
    ((rightFunctor R).obj (Opposite.op M)).obj (Opposite.op P) =
      CharacterModule.moduleObj R (P ⊗ M) := sorry

/-- On a map `f : M ⟶ N`, the component of `rightFunctor R` at `Pᵒᵖ` is the
character-dual map induced by `𝟙 P ⊗ₘ f`. -/
theorem rightFunctor_map_app {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (P : ModuleCat.{u} R) :
    ((rightFunctor R).map f.op).app (Opposite.op P) =
      CharacterModule.dualMap R (𝟙 P ⊗ₘ f) := sorry

/-- Transport postcomposition by `g` through character tensor–Hom duality at `P`. -/
noncomputable def sectionApp {M N : ModuleCat.{u} R}
    (g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N)
    (P : ModuleCat.{u} R) :
    ((rightFunctor R).obj (Opposite.op M)).obj (Opposite.op P) ⟶
      ((rightFunctor R).obj (Opposite.op N)).obj (Opposite.op P) :=
  (appIso R (Opposite.op (P, M))).hom ≫
    ((linearYoneda R (ModuleCat.{u} R)).map g).app (Opposite.op P) ≫
      (appIso R (Opposite.op (P, N))).inv

/-- Under character tensor–Hom duality, `sectionApp R g P` is postcomposition by `g`. -/
theorem sectionApp_equiv {M N : ModuleCat.{u} R}
    (g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N)
    (P : ModuleCat.{u} R)
    (χ : ((rightFunctor R).obj (Opposite.op M)).obj (Opposite.op P)) :
    appEquiv R (Opposite.op (P, N)) (sectionApp R g P χ) =
      appEquiv R (Opposite.op (P, M)) χ ≫ g := sorry

/-- The transported postcomposition maps are natural in the tensor factor `P`. -/
theorem sectionApp_naturality {M N P Q : ModuleCat.{u} R}
    (g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N)
    (p : P ⟶ Q) :
    ((rightFunctor R).obj (Opposite.op M)).map p.op ≫ sectionApp R g P =
      sectionApp R g Q ≫ ((rightFunctor R).obj (Opposite.op N)).map p.op := sorry

/-- Postcomposition by `g`, transported pointwise through character tensor–Hom duality,
as a natural transformation in `P`. -/
noncomputable def sectionNatTrans {M N : ModuleCat.{u} R}
    (g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N) :
    (rightFunctor R).obj (Opposite.op M) ⟶
      (rightFunctor R).obj (Opposite.op N) where
  app P := sectionApp R g P.unop
  naturality _ _ p := sectionApp_naturality R g p.unop

/-- The components of `sectionNatTrans R g` are the explicitly transported maps. -/
theorem sectionNatTrans_app {M N : ModuleCat.{u} R}
    (g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N)
    (P : ModuleCat.{u} R) :
    (sectionNatTrans R g).app (Opposite.op P) = sectionApp R g P := sorry

/-- A chosen splitting of `CharacterModule.dualMap R f` splits the induced morphism
between the functors of tensor factors. -/
theorem sectionNatTrans_comp {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (s : SplitEpi (CharacterModule.dualMap R f)) :
    sectionNatTrans R s.section_ ≫ (rightFunctor R).map f.op =
      𝟙 ((rightFunctor R).obj (Opposite.op M)) := sorry

/-- The chosen functorial splitting induced by a splitting of the character-dual map. -/
noncomputable def splitEpi {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (s : SplitEpi (CharacterModule.dualMap R f)) :
    SplitEpi ((rightFunctor R).map f.op) where
  section_ := sectionNatTrans R s.section_
  id := sectionNatTrans_comp R f s

/-- The chosen section in `splitEpi R f s` has the explicitly transported components. -/
theorem splitEpi_section_app {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (s : SplitEpi (CharacterModule.dualMap R f)) (P : ModuleCat.{u} R) :
    (splitEpi R f s).section_.app (Opposite.op P) =
      sectionApp R s.section_ P := sorry

end CharacterModule.TensorHom
