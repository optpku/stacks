/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_15_1

/-!
# Semi-representable localization comparison

For `K` in `SR(C)`, sheaves on `OverSite K` are compared with objects of `Sh(C, J)` over
`sheafified J K`, the sheafification of `FormalCoproduct.toPresheaf.obj K`.  The comparison
upgrades localization lower shriek `j_!` to a functor into the slice, and identifies `j⁻¹`
and relocalization inverse image with `Over.star` and `Over.pullback`.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open FormalCoproduct (toPresheaf toPresheafObjMk)
open SemiRepresentableFamily (OverSite overIncl overTopology overMap overMap_comp_incl forget_comp_incl)

universe w v u

noncomputable section

namespace CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/-- The sheafification of the presheaf `F(K)` attached to a semi-representable family by
Hypercoverings, Definition 25.2.2. -/
def sheafified [HasWeakSheafify J (Type (max w v))] (K : FormalCoproduct.{w} C) :
    Sheaf J (Type (max w v)) :=
  (presheafToSheaf J (Type (max w v))).obj (toPresheaf.obj K)

/-- A morphism of semi-representable families induces the corresponding map of sheafified
associated presheaves. -/
def sheafifiedMap [HasWeakSheafify J (Type (max w v))]
    {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) :
    sheafified J K ⟶ sheafified J L :=
  (presheafToSheaf J (Type (max w v))).map (toPresheaf.map φ)

/-- Sheafification of the associated presheaf sends identity morphisms of semi-representable
families to identity morphisms. -/
theorem sheafifiedMap_id [HasWeakSheafify J (Type (max w v))] (K : FormalCoproduct.{w} C) :
    sheafifiedMap J (𝟙 K) = 𝟙 (sheafified J K) := sorry

/-- Sheafification of the associated presheaf preserves composition of morphisms of
semi-representable families. -/
theorem sheafifiedMap_comp [HasWeakSheafify J (Type (max w v))]
    {K L M : FormalCoproduct.{w} C} (φ : K ⟶ L) (ψ : L ⟶ M) :
    sheafifiedMap J (φ ≫ ψ) = sheafifiedMap J φ ≫ sheafifiedMap J ψ := sorry

/-- Relocalization followed by localization at `L` recovers localization at `K`. -/
def overMap_forget {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) :
    overMap φ ⋙ SemiRepresentableFamily.forget L ≅ SemiRepresentableFamily.forget K :=
  CategoryTheory.Sigma.natIso fun i ↦
    (Functor.associator (overIncl K i) (overMap φ)
        (SemiRepresentableFamily.forget L)).symm ≪≫
      Functor.isoWhiskerRight (overMap_comp_incl φ i) (SemiRepresentableFamily.forget L) ≪≫
        Functor.associator (Over.map (φ.φ i)) (overIncl L (φ.f i))
          (SemiRepresentableFamily.forget L) ≪≫
          Functor.isoWhiskerLeft (Over.map (φ.φ i)) (forget_comp_incl L (φ.f i)) ≪≫
            Over.mapForget (φ.φ i) ≪≫ (forget_comp_incl K i).symm

/-- Relocalization then localization at `L` agrees on objects with localization at `K`. -/
theorem overMap_forget_obj {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) (X : OverSite K) :
    (SemiRepresentableFamily.forget L).obj ((overMap φ).obj X) =
      (SemiRepresentableFamily.forget K).obj X := sorry

variable (K : FormalCoproduct.{w} C)
variable [HasWeakSheafify J (Type (max w v))]
variable [HasWeakSheafify (overTopology J K) (Type (max w v))]
variable [∀ G : (OverSite K)ᵒᵖ ⥤ Type (max w v),
  (SemiRepresentableFamily.forget K).op.HasLeftKanExtension G]

/-- The canonical section of `j^* F(K)` at an object of `OverSite K`, given by the component
structure map as a summand of `toPresheaf.obj K`. -/
def inverseImageSummand (X : (OverSite K)ᵒᵖ) :
    (toPresheaf.obj K).obj (op ((SemiRepresentableFamily.forget K).obj X.unop)) :=
  toPresheafObjMk K (op ((SemiRepresentableFamily.forget K).obj X.unop))
    X.unop.1 X.unop.2.hom

/-- The component at `X` of the canonical map from the terminal sheaf on `C / K` to
`j^{-1} (F(K)^#)`. -/
def terminalToInverseImageApp (X : (OverSite K)ᵒᵖ) :
    (Sheaf.terminal (overTopology J K) Types.isTerminalPUnit.{max w v}).obj.obj X ⟶
      (((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
          (Type (max w v)) (overTopology J K) J).obj (sheafified J K)).obj.obj X :=
  TypeCat.ofHom fun _ ↦
    ((sheafificationAdjunction J (Type (max w v))).unit.app (toPresheaf.obj K)).app
      (op ((SemiRepresentableFamily.forget K).obj X.unop)) (inverseImageSummand K X)

/-- The components of `terminalToInverseImage` are natural. -/
theorem terminalToInverseImageApp_naturality {X Y : (OverSite K)ᵒᵖ} (f : X ⟶ Y) :
    (Sheaf.terminal (overTopology J K) Types.isTerminalPUnit.{max w v}).obj.map f ≫
        terminalToInverseImageApp J K Y =
      terminalToInverseImageApp J K X ≫
        (((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
            (Type (max w v)) (overTopology J K) J).obj (sheafified J K)).obj.map f := sorry

/-- The canonical map from the terminal sheaf on `C / K` to `j^{-1} (F(K)^#)`. -/
def terminalToInverseImage :
    Sheaf.terminal (overTopology J K) Types.isTerminalPUnit.{max w v} ⟶
      ((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
        (Type (max w v)) (overTopology J K) J).obj (sheafified J K) where
  hom :=
    NatTrans.mk (terminalToInverseImageApp J K)
      (fun {_ _} f ↦ terminalToInverseImageApp_naturality J K f)

/-- The adjunct of `terminalToInverseImage`, giving `j_!` of the terminal sheaf on `C / K`
as a map to `F(K)^#`. -/
def terminalComparison :
    ((SemiRepresentableFamily.forget K).sheafPullback
        (Type (max w v)) (overTopology J K) J).obj
      (Sheaf.terminal (overTopology J K) Types.isTerminalPUnit.{max w v}) ⟶
      sheafified J K :=
  ((SemiRepresentableFamily.forget K).sheafPullback
        (Type (max w v)) (overTopology J K) J).map (terminalToInverseImage J K) ≫
    ((SemiRepresentableFamily.forget K).sheafAdjunctionContinuous
        (Type (max w v)) (overTopology J K) J).counit.app (sheafified J K)

/-- The structure morphism of the comparison, sending localized lower shriek of a sheaf on
`C / K` to `F(K)^#` by the unique map to the terminal sheaf. -/
def comparisonHom (G : Sheaf (overTopology J K) (Type (max w v))) :
    ((SemiRepresentableFamily.forget K).sheafPullback
        (Type (max w v)) (overTopology J K) J).obj G ⟶
      sheafified J K :=
  ((SemiRepresentableFamily.forget K).sheafPullback
        (Type (max w v)) (overTopology J K) J).map
      ((Sheaf.isTerminalTerminal (overTopology J K) Types.isTerminalPUnit.{max w v}).from G) ≫
    terminalComparison J K

/-- The maps `comparisonHom` are natural in the sheaf on `C / K`. -/
theorem comparisonHom_naturality {G G' : Sheaf (overTopology J K) (Type (max w v))}
    (f : G ⟶ G') :
    ((SemiRepresentableFamily.forget K).sheafPullback
          (Type (max w v)) (overTopology J K) J).map f ≫
        comparisonHom J K G' =
      comparisonHom J K G := sorry

/-- The comparison functor `j_!` as a functor into the slice over `F(K)^#`. -/
def comparison :
    Sheaf (overTopology J K) (Type (max w v)) ⥤ Over (sheafified J K) :=
  ((SemiRepresentableFamily.forget K).sheafPullback
      (Type (max w v)) (overTopology J K) J).toOver
    (sheafified J K) (comparisonHom J K) (comparisonHom_naturality J K)

namespace comparison

/-- Forgetting the structure morphism of semi-representable localization recovers localization
lower shriek `j_!`. -/
@[simp]
theorem forget :
    comparison J K ⋙ Over.forget (sheafified J K) =
      (SemiRepresentableFamily.forget K).sheafPullback (Type (max w v))
        (overTopology J K) J :=
  rfl

/-- The semi-representable localization comparison is an equivalence. -/
theorem isEquivalence : Functor.IsEquivalence (comparison J K) := sorry

end comparison

section InverseImage

variable [HasBinaryProducts (Sheaf J (Type (max w v)))]

/-- The underlying map of the inverse-image comparison respects the maps to `F(K)^#`. -/
theorem inverseImageComparisonApp_comm (F : Sheaf J (Type (max w v))) :
    prod.lift
        (comparisonHom J K
          (((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
              (Type (max w v)) (overTopology J K) J).obj F))
        (((SemiRepresentableFamily.forget K).sheafAdjunctionContinuous
            (Type (max w v)) (overTopology J K) J).counit.app F) ≫
      ((Over.star (sheafified J K)).obj F).hom =
    ((comparison J K).obj
      (((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
          (Type (max w v)) (overTopology J K) J).obj F)).hom := sorry

/-- The component of the comparison from inverse image along `j` to the slice functor
`Over.star (F(K)^#)`. -/
def inverseImageComparisonApp (F : Sheaf J (Type (max w v))) :
    ((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
          (Type (max w v)) (overTopology J K) J ⋙
        comparison J K).obj F ⟶
      (Over.star (sheafified J K)).obj F :=
  Over.homMk
    (prod.lift
      (comparisonHom J K
        (((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
            (Type (max w v)) (overTopology J K) J).obj F))
      (((SemiRepresentableFamily.forget K).sheafAdjunctionContinuous
          (Type (max w v)) (overTopology J K) J).counit.app F))
    (inverseImageComparisonApp_comm J K F)

/-- The inverse-image comparison components are natural in the ambient sheaf. -/
theorem inverseImageComparisonApp_naturality {F G : Sheaf J (Type (max w v))} (η : F ⟶ G) :
    ((SemiRepresentableFamily.forget K).sheafPushforwardContinuous
            (Type (max w v)) (overTopology J K) J ⋙
          comparison J K).map η ≫
        inverseImageComparisonApp J K G =
      inverseImageComparisonApp J K F ≫ (Over.star (sheafified J K)).map η := sorry

/-- Via the comparison of clause (1), inverse image along `j` corresponds to
`Over.star (F(K)^#)`. -/
def inverseImageComparison :
    (SemiRepresentableFamily.forget K).sheafPushforwardContinuous
        (Type (max w v)) (overTopology J K) J ⋙
        comparison J K ⟶
      Over.star (sheafified J K) :=
  NatTrans.mk
    (inverseImageComparisonApp J K)
    (fun {_ _} η ↦ inverseImageComparisonApp_naturality J K η)

/-- The inverse-image comparison to `Over.star (F(K)^#)` is invertible. -/
theorem inverseImageComparison_isIso : IsIso (inverseImageComparison J K) := sorry

end InverseImage

variable (L : FormalCoproduct.{w} C) (φ : K ⟶ L)
variable [HasWeakSheafify (overTopology J L) (Type (max w v))]
variable [∀ G : (OverSite L)ᵒᵖ ⥤ Type (max w v),
  (SemiRepresentableFamily.forget L).op.HasLeftKanExtension G]
variable [∀ G : (OverSite K)ᵒᵖ ⥤ Type (max w v), (overMap φ).op.HasLeftKanExtension G]
variable [HasPullbacksAlong (sheafifiedMap J φ)]

/-- The mate-oriented relocalization comparison commutes with the maps to the target slice. -/
theorem relocalizationLowerShriekComparisonApp_comm
    (G : Sheaf (overTopology J K) (Type (max w v))) :
    (Functor.sheafPullbackComp' (overTopology J K) (overTopology J L) J
          (overMap φ) (SemiRepresentableFamily.forget L) (overMap_forget φ)).inv.app G ≫
        (((overMap φ).sheafPullback (Type (max w v)) (overTopology J K) (overTopology J L) ⋙
          comparison J L).obj G).hom =
      ((comparison J K ⋙ Over.map (sheafifiedMap J φ)).obj G).hom := sorry

/-- The component of the mate-oriented relocalization lower-shriek comparison. -/
def relocalizationLowerShriekComparisonApp
    (G : Sheaf (overTopology J K) (Type (max w v))) :
    (comparison J K ⋙ Over.map (sheafifiedMap J φ)).obj G ⟶
      ((overMap φ).sheafPullback (Type (max w v)) (overTopology J K) (overTopology J L) ⋙
        comparison J L).obj G :=
  Over.homMk
    ((Functor.sheafPullbackComp' (overTopology J K) (overTopology J L) J
        (overMap φ) (SemiRepresentableFamily.forget L) (overMap_forget φ)).inv.app G)
    (relocalizationLowerShriekComparisonApp_comm J K L φ G)

/-- The mate-oriented relocalization components are natural. -/
theorem relocalizationLowerShriekComparisonApp_naturality
    {G G' : Sheaf (overTopology J K) (Type (max w v))} (η : G ⟶ G') :
    (comparison J K ⋙ Over.map (sheafifiedMap J φ)).map η ≫
        relocalizationLowerShriekComparisonApp J K L φ G' =
      relocalizationLowerShriekComparisonApp J K L φ G ≫
        ((overMap φ).sheafPullback (Type (max w v)) (overTopology J K) (overTopology J L) ⋙
          comparison J L).map η := sorry

/-- Postcomposition by `sheafifiedMap φ` is relocalization lower shriek under the
semi-representable localization comparisons. -/
def relocalizationLowerShriekComparison :
    comparison J K ⋙ Over.map (sheafifiedMap J φ) ⟶
      (overMap φ).sheafPullback (Type (max w v)) (overTopology J K) (overTopology J L) ⋙
        comparison J L :=
  NatTrans.mk
    (relocalizationLowerShriekComparisonApp J K L φ)
    (fun {_ _} η ↦ relocalizationLowerShriekComparisonApp_naturality J K L φ η)

/-- The two maps used to lift to the pullback along `sheafifiedMap φ` agree after composing
to `F(L)^#`. -/
theorem relocalizationInverseImageComparisonApp_lift_comm
    (G : Sheaf (overTopology J L) (Type (max w v))) :
    ((Functor.sheafPullbackComp' (overTopology J K) (overTopology J L) J
          (overMap φ) (SemiRepresentableFamily.forget L) (overMap_forget φ)).inv.app
        (((overMap φ).sheafPushforwardContinuous (Type (max w v))
            (overTopology J K) (overTopology J L)).obj G) ≫
      ((SemiRepresentableFamily.forget L).sheafPullback
          (Type (max w v)) (overTopology J L) J).map
        (((overMap φ).sheafAdjunctionContinuous (Type (max w v))
            (overTopology J K) (overTopology J L)).counit.app G)) ≫
      ((comparison J L).obj G).hom =
    comparisonHom J K
        (((overMap φ).sheafPushforwardContinuous (Type (max w v))
            (overTopology J K) (overTopology J L)).obj G) ≫
      sheafifiedMap J φ := sorry

/-- The underlying map of the relocalization inverse-image comparison lands in the
pullback of `j_! G` along `sheafifiedMap φ`. -/
theorem relocalizationInverseImageComparisonApp_comm
    (G : Sheaf (overTopology J L) (Type (max w v))) :
    pullback.lift
        ((Functor.sheafPullbackComp' (overTopology J K) (overTopology J L) J
              (overMap φ) (SemiRepresentableFamily.forget L) (overMap_forget φ)).inv.app
            (((overMap φ).sheafPushforwardContinuous (Type (max w v))
                (overTopology J K) (overTopology J L)).obj G) ≫
          ((SemiRepresentableFamily.forget L).sheafPullback
              (Type (max w v)) (overTopology J L) J).map
            (((overMap φ).sheafAdjunctionContinuous (Type (max w v))
                (overTopology J K) (overTopology J L)).counit.app G))
        (comparisonHom J K
          (((overMap φ).sheafPushforwardContinuous (Type (max w v))
              (overTopology J K) (overTopology J L)).obj G))
        (relocalizationInverseImageComparisonApp_lift_comm J K L φ G) ≫
      ((Over.pullback (sheafifiedMap J φ)).obj ((comparison J L).obj G)).hom =
    ((comparison J K).obj
      (((overMap φ).sheafPushforwardContinuous (Type (max w v))
          (overTopology J K) (overTopology J L)).obj G)).hom := sorry

/-- The component of the comparison from relocalization inverse image to pullback along
`F(K)^# ⟶ F(L)^#`. -/
def relocalizationInverseImageComparisonApp
    (G : Sheaf (overTopology J L) (Type (max w v))) :
    ((overMap φ).sheafPushforwardContinuous (Type (max w v))
          (overTopology J K) (overTopology J L) ⋙
        comparison J K).obj G ⟶
      (comparison J L ⋙ Over.pullback (sheafifiedMap J φ)).obj G :=
  Over.homMk
    (pullback.lift
      ((Functor.sheafPullbackComp' (overTopology J K) (overTopology J L) J
            (overMap φ) (SemiRepresentableFamily.forget L) (overMap_forget φ)).inv.app
          (((overMap φ).sheafPushforwardContinuous (Type (max w v))
              (overTopology J K) (overTopology J L)).obj G) ≫
        ((SemiRepresentableFamily.forget L).sheafPullback
            (Type (max w v)) (overTopology J L) J).map
          (((overMap φ).sheafAdjunctionContinuous (Type (max w v))
              (overTopology J K) (overTopology J L)).counit.app G))
      (comparisonHom J K
        (((overMap φ).sheafPushforwardContinuous (Type (max w v))
            (overTopology J K) (overTopology J L)).obj G))
      (relocalizationInverseImageComparisonApp_lift_comm J K L φ G))
    (relocalizationInverseImageComparisonApp_comm J K L φ G)

/-- The relocalization inverse-image comparison components are natural. -/
theorem relocalizationInverseImageComparisonApp_naturality
    {G G' : Sheaf (overTopology J L) (Type (max w v))} (η : G ⟶ G') :
    ((overMap φ).sheafPushforwardContinuous (Type (max w v))
            (overTopology J K) (overTopology J L) ⋙
          comparison J K).map η ≫
        relocalizationInverseImageComparisonApp J K L φ G' =
      relocalizationInverseImageComparisonApp J K L φ G ≫
        (comparison J L ⋙ Over.pullback (sheafifiedMap J φ)).map η := sorry

/-- Via the comparisons of clause (1), inverse image along relocalization corresponds to
pullback along `F(K)^# ⟶ F(L)^#`. -/
def relocalizationInverseImageComparison :
    (overMap φ).sheafPushforwardContinuous (Type (max w v))
        (overTopology J K) (overTopology J L) ⋙
        comparison J K ⟶
      comparison J L ⋙ Over.pullback (sheafifiedMap J φ) :=
  NatTrans.mk
    (relocalizationInverseImageComparisonApp J K L φ)
    (fun {_ _} η ↦ relocalizationInverseImageComparisonApp_naturality J K L φ η)

/-- The inverse-image relocalization comparison is invertible. -/
theorem relocalizationInverseImageComparison_isIso :
    IsIso (relocalizationInverseImageComparison J K L φ) := sorry

end CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization
