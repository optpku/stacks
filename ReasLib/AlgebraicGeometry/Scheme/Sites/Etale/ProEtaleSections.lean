/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Glueing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison

/-!
# Formula presheaf for étale-to-pro-étale inverse image

The assignment sending a weakly étale `f : Y ⟶ X` to the global étale
sections of `f_étale⁻¹ F`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallGlueing
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z),
  ∀ P : Z.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback f).op.HasLeftKanExtension P]

variable {X : Scheme.{u}}

/-- The morphism from a weakly étale `X`-scheme to the identity object of
`Over X`. -/
def etalePullbackGammaOverHom (Y : X.ProEt) :
    (ProEt.forget X).obj Y ⟶ Over.mk (𝟙 X) :=
  Over.homMk Y.hom

/-- The underlying scheme morphism of `etalePullbackGammaOverHom` is the
structure morphism. -/
theorem etalePullbackGammaOverHom_left (Y : X.ProEt) :
    (etalePullbackGammaOverHom Y).left = Y.hom :=
  sorry

/-- Inverse image of sheaves of sets along small étale base change, as a
Glueing pullback from the identity object of `Over X`. -/
abbrev etaleSmallSheafPullback (Y : X.ProEt) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf Y.left.smallEtaleTopology (Type (u + 1)) :=
  pullback (etalePullbackGammaOverHom Y)

/-- Global sections of the small étale inverse image of `F` on a weakly étale
`X`-scheme. -/
def etalePullbackGammaObj (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (Y : X.ProEt) : Type (u + 1) :=
  ((etaleSmallSheafPullback Y).obj F).obj.obj (op (Etale.globalEtale Y.left))

/-- The formula object agrees with global sections of `f_étale⁻¹ F`. -/
theorem etalePullbackGammaObj_inverseImage
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt) :
    IsIsomorphic (etalePullbackGammaObj F Y)
      ((((smallMorphism Y.hom)⁻¹).obj F).obj.obj (op (Etale.globalEtale Y.left))) :=
  sorry

/-- Successive Glueing pullbacks along a morphism of weakly étale `X`-schemes
identify with pullback along the source structure morphism. -/
def etalePullbackGammaCompIso {Y Y' : X.ProEt} (φ : Y' ⟶ Y) :
    etaleSmallSheafPullback Y ⋙ pullback ((ProEt.forget X).map φ) ≅
      etaleSmallSheafPullback Y' :=
  pullbackComp (etalePullbackGammaOverHom Y) ((ProEt.forget X).map φ) ≪≫
    eqToIso
      (congrArg pullback
        (CategoryTheory.Over.OverMorphism.ext
          (MorphismProperty.Over.w φ)))

/-- Restriction of the formula sections along a morphism of weakly étale
`X`-schemes. -/
def etalePullbackGammaMap (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Y Y' : X.ProEt} (φ : Y' ⟶ Y) :
    etalePullbackGammaObj F Y ⟶ etalePullbackGammaObj F Y' :=
  ConcreteCategory.ofHom <| TypeCat.Fun.mk fun σ ↦
    (((etalePullbackGammaCompIso φ).hom.app F).hom.app (op (Etale.globalEtale Y'.left))
      (Etale.restrictGlobalSection φ.left ((etaleSmallSheafPullback Y).obj F) σ) :
      etalePullbackGammaObj F Y')

/-- The formula `(f : Y ⟶ X) ↦ Γ(Y.Etale, f_étale⁻¹ F)` as a presheaf of sets
on the small pro-étale site of `X`. -/
def etalePullbackGamma (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    X.ProEtᵒᵖ ⥤ Type (u + 1) where
  obj Y := etalePullbackGammaObj F Y.unop
  map φ := etalePullbackGammaMap F φ.unop
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The formula presheaf evaluates at `Y` as `etalePullbackGammaObj`. -/
theorem etalePullbackGamma_obj (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (Y : X.ProEt) :
    (etalePullbackGamma F).obj (op Y) = etalePullbackGammaObj F Y :=
  sorry

/-- Restriction maps of the formula presheaf are the maps
`etalePullbackGammaMap`. -/
theorem etalePullbackGamma_map (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Y Y' : X.ProEt} (φ : Y' ⟶ Y) :
    (etalePullbackGamma F).map φ.op = etalePullbackGammaMap F φ :=
  sorry

end AlgebraicGeometry.Scheme
