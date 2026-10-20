/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafHom
public import ReasLib.CategoryTheory.Sites.LocallyConstant.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local morphisms between module-valued sheaves

This file lifts Mathlib's type-valued `CategoryTheory.sheafHom'` to the natural
module-valued local-Hom sheaf for sheaves of modules over a fixed commutative ring.  It also
constructs the sheaf of local isomorphisms and records their locally constant behavior.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]

namespace LocalHom

variable (F G : Sheaf J (ModuleCat.{max u v w} Λ))

/-- Restriction of local morphisms is additive. -/
theorem restrict_add {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ ψ : F.over X.unop ⟶ G.over X.unop) :
    (J.overMapPullback (ModuleCat.{max u v w} Λ) f.unop).map (φ + ψ) =
      (J.overMapPullback (ModuleCat.{max u v w} Λ) f.unop).map φ +
        (J.overMapPullback (ModuleCat.{max u v w} Λ) f.unop).map ψ := sorry

/-- Restriction of local morphisms commutes with scalar multiplication. -/
theorem restrict_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : Λ)
    (φ : F.over X.unop ⟶ G.over X.unop) :
    (J.overMapPullback (ModuleCat.{max u v w} Λ) f.unop).map (r • φ) =
      r • (J.overMapPullback (ModuleCat.{max u v w} Λ) f.unop).map φ := sorry

/-- The linear restriction map between modules of local morphisms. -/
@[stacks 093T "local Hom restriction"]
noncomputable def restrict {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (F.over X.unop ⟶ G.over X.unop) →ₗ[Λ]
      (F.over Y.unop ⟶ G.over Y.unop) :=
  { toFun := (J.overMapPullback (ModuleCat.{max u v w} Λ) f.unop).map
    map_add' := restrict_add F G f
    map_smul' := restrict_smul F G f }

/-- Applying the linear restriction map agrees with applying the slice pullback functor. -/
@[simp]
theorem restrict_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ⟶ G.over X.unop) :
    restrict F G f φ =
      (J.overMapPullback (ModuleCat.{max u v w} Λ) f.unop).map φ := sorry

/-- A component of a restricted local morphism is obtained by reindexing the slice object. -/
theorem restrict_app {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ⟶ G.over X.unop) (U : (Over Y.unop)ᵒᵖ) :
    (restrict F G f φ).hom.app U =
      φ.hom.app (op ((Over.map f.unop).obj U.unop)) := sorry

/-- The bundled local-Hom restriction map respects identity morphisms. -/
theorem map_id (X : Cᵒᵖ) :
    ModuleCat.ofHom (restrict F G (𝟙 X)) =
      𝟙 (ModuleCat.of Λ (F.over X.unop ⟶ G.over X.unop)) := sorry

/-- The bundled local-Hom restriction maps respect composition. -/
theorem map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ModuleCat.ofHom (restrict F G (f ≫ g)) =
      ModuleCat.ofHom (restrict F G f) ≫ ModuleCat.ofHom (restrict F G g) := sorry

/-- The presheaf of modules of local morphisms between `F` and `G`. -/
@[stacks 093T "local Hom presheaf"]
noncomputable def presheaf : Cᵒᵖ ⥤ ModuleCat.{max u v w} Λ where
  obj X := ModuleCat.of Λ (F.over X.unop ⟶ G.over X.unop)
  map f := ModuleCat.ofHom (restrict F G f)
  map_id := map_id F G
  map_comp := map_comp F G

/-- Forgetting the module structure on the local-Hom presheaf recovers Mathlib's canonical
type-valued local-Hom presheaf. -/
theorem presheaf_comp_forget :
    presheaf F G ⋙ forget (ModuleCat.{max u v w} Λ) = sheafHom' F G := sorry

/-- The module-valued local-Hom presheaf satisfies the sheaf condition. -/
theorem presheaf_isSheaf : Presheaf.IsSheaf J (presheaf F G) := sorry

/-- The sheaf of modules of local morphisms between `F` and `G`. -/
@[stacks 093T "local Hom sheaf"]
noncomputable def sheaf : Sheaf J (ModuleCat.{max u v w} Λ) :=
  ⟨presheaf F G, presheaf_isSheaf F G⟩

/-- Sections of the local-Hom sheaf at `X` are morphisms between the restrictions to `J.over X`. -/
theorem sheaf_obj (X : Cᵒᵖ) :
    (sheaf F G).1.obj X = ModuleCat.of Λ (F.over X.unop ⟶ G.over X.unop) := sorry

end LocalHom

namespace LocalIso

variable {D : Type w} [Category.{z} D]
variable (F G : Sheaf J D)

/-- The function restricting a local isomorphism along a morphism of the base site. -/
@[stacks 093T "local isomorphism restriction function"]
noncomputable def restrictFun {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (F.over X.unop ≅ G.over X.unop) →
      (F.over Y.unop ≅ G.over Y.unop) :=
  fun e ↦ (J.overMapPullback D f.unop).mapIso e

/-- Restriction of local isomorphisms, bundled as a morphism in `Type`. -/
@[stacks 093T "local isomorphism restriction"]
noncomputable def restrict {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (F.over X.unop ≅ G.over X.unop) ⟶
      (F.over Y.unop ≅ G.over Y.unop) :=
  TypeCat.ofHom (restrictFun F G f)

/-- Applying bundled restriction agrees with the underlying restriction function. -/
@[simp]
theorem restrict_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : F.over X.unop ≅ G.over X.unop) :
    restrict F G f e = restrictFun F G f e := sorry

/-- The forward morphism of a restricted local isomorphism is the restricted forward morphism. -/
@[simp]
theorem restrict_hom {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : F.over X.unop ≅ G.over X.unop) :
    (restrict F G f e).hom =
      (J.overMapPullback D f.unop).map e.hom := sorry

/-- The inverse morphism of a restricted local isomorphism is the restricted inverse morphism. -/
@[simp]
theorem restrict_inv {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : F.over X.unop ≅ G.over X.unop) :
    (restrict F G f e).inv =
      (J.overMapPullback D f.unop).map e.inv := sorry

/-- A component of the forward map of a restricted local isomorphism is obtained by reindexing
the slice object. -/
theorem restrict_hom_app {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : F.over X.unop ≅ G.over X.unop) (U : (Over Y.unop)ᵒᵖ) :
    (restrict F G f e).hom.hom.app U =
      e.hom.hom.app (op ((Over.map f.unop).obj U.unop)) := sorry

/-- Restriction of local isomorphisms respects identity morphisms. -/
theorem map_id (X : Cᵒᵖ) : restrict F G (𝟙 X) = 𝟙 _ := sorry

/-- Restriction of local isomorphisms respects composition. -/
theorem map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrict F G (f ≫ g) = restrict F G f ≫ restrict F G g := sorry

/-- The presheaf of local isomorphisms between two category-valued sheaves. -/
@[stacks 093T "local isomorphism presheaf"]
noncomputable def presheaf : Cᵒᵖ ⥤ Type (max u v z) where
  obj X := F.over X.unop ≅ G.over X.unop
  map f := restrict F G f
  map_id := map_id F G
  map_comp := map_comp F G

/-- The presheaf of local isomorphisms satisfies the sheaf condition. -/
theorem presheaf_isSheaf : Presheaf.IsSheaf J (presheaf F G) := sorry

/-- The sheaf of local isomorphisms between two category-valued sheaves. -/
@[stacks 093T "local isomorphism sheaf"]
noncomputable def sheaf : Sheaf J (Type (max u v z)) :=
  ⟨presheaf F G, presheaf_isSheaf F G⟩

/-- Sections of the local-isomorphism sheaf at `X` are isomorphisms between the restrictions to
`J.over X`. -/
theorem sheaf_obj (X : Cᵒᵖ) :
    (sheaf F G).1.obj X = (F.over X.unop ≅ G.over X.unop) := sorry

end LocalIso

section ConstantComparisons

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]

/-- For a finitely presented module `M`, local morphisms
between the constant sheaves on `M` and `N` form the constant sheaf on `M ⟶ N`. -/
@[stacks 093T "(1)"]
theorem LocalHom.isIsomorphic_constant
    (M N : ModuleCat.{max u v w} Λ) [Module.FinitePresentation Λ M] :
    IsIsomorphic
      (LocalHom.sheaf
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj N))
      ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj
        (ModuleCat.of Λ (M ⟶ N))) := sorry

variable [HasWeakSheafify J (Type (max u v w))]

/-- For finitely presented modules `M` and `N`, local
isomorphisms between their constant sheaves form the constant sheaf on `M ≅ N`. -/
@[stacks 093T "(2)"]
theorem LocalIso.isIsomorphic_constant
    (M N : ModuleCat.{max u v w} Λ)
    [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N] :
    IsIsomorphic
      (LocalIso.sheaf
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj N))
      ((constantSheaf J (Type (max u v w))).obj (M ≅ N)) := sorry

end ConstantComparisons

section LocallyConstantComparisons

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]

/-- Local Hom from a locally constant module sheaf with finitely
presented constant models to a locally constant module sheaf is locally constant. -/
@[stacks 093T "(3)"]
theorem LocalHom.isLocallyConstant
    (F G : Sheaf J (ModuleCat.{max u v w} Λ))
    [LocallyConstant.IsFinitePresentation F] [IsLocallyConstant G] :
    IsLocallyConstant (LocalHom.sheaf F G) := sorry

variable [HasWeakSheafify J (Type (max u v w))]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type (max u v w))]

/-- Local isomorphisms between locally constant module sheaves with
finitely presented constant models form a locally constant sheaf of types. -/
@[stacks 093T "(4)"]
theorem LocalIso.isLocallyConstant
    (F G : Sheaf J (ModuleCat.{max u v w} Λ))
    [LocallyConstant.IsFinitePresentation F]
    [LocallyConstant.IsFinitePresentation G] :
    IsLocallyConstant (LocalIso.sheaf F G) := sorry

end LocallyConstantComparisons

end CategoryTheory.Sheaf
