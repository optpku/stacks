/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace OpenHomRestrictionComparison
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
variable [X.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]

/-- The actual cartesian projection, regarded as an etale morphism over Y. -/
def siteProjection (V : Y.Etale) :
    (etaleRestriction j).obj ((smallEtalePullback j).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom j) (by exact pullback.condition)

/-- Restrict sections along that projection. This is the actual j*⊣j_* unit,
with j* spelled as the pointwise etale restriction functor. -/
def unit (S : Type (u + 1)) [Ring S]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)) : F ⟶
    (LocalHomDirectImage.pushforward j S).obj ((etaleRestrictionSheaf j (ModuleCat.{u + 1} S)).obj F) :=
  ObjectProperty.homMk
    { app := fun U ↦ F.obj.map (siteProjection j U.unop).op
      naturality := by sorry }

variable (B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
variable (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

abbrev closedSource := (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).obj
  (NoncommLocalHom.obj h hc X ((etaleRestrictionSheaf j (ModuleCat.{u + 1} R)).obj B) J)
abbrev closedTarget := NoncommLocalHom.obj h hc Y B ((LocalHomDirectImage.pushforward j A).obj J)

/-- The closed restriction/direct-image map evaluates on the explicitly
pulled-back chart after the displayed unit, retaining right R scalars. -/
def closedSection (U : Y.Etaleᵒᵖ) (α : (closedSource h hc j B J).obj.obj U) :
    (closedTarget h hc j B J).obj.obj U :=
  { app := fun V ↦ (NoncommLocalHom.modules h).map ((unit j R B).hom.app (op V.unop.left)) ≫
      α.app (op (Over.mk ((smallEtalePullback j).map V.unop.hom)))
    naturality := by sorry }

def closedComparison : closedSource h hc j B J ⟶ closedTarget h hc j B J :=
  ObjectProperty.homMk
    { app := fun U ↦ ConcreteCategory.ofHom (C := ModuleCat.{u + 1} Rᵐᵒᵖ)
        { toFun := closedSection h hc j B J U
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

instance closedComparison_isIso : IsIso (closedComparison h hc j B J) := by sorry

def closedIso : closedSource h hc j B J ≅ closedTarget h hc j B J :=
  @asIso _ _ _ _ (closedComparison h hc j B J) (closedComparison_isIso h hc j B J)

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R, (etaleRestriction j).op.HasLeftKanExtension F]
variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
variable (K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- Actual open-immersion Hom comparison: postcompose with the restriction
unit of K, use the closed adjunction, then precompose with the j!-restriction
unit of F. Neither Hom object nor either direction is arbitrarily selected. -/
def comparison :
    NoncommLocalHom.obj h hc Y ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).obj F) K ⟶
    (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).obj
      (NoncommLocalHom.obj h hc X F ((etaleRestrictionSheaf j (ModuleCat.{u + 1} A)).obj K)) :=
  NoncommLocalHom.postcomp h hc Y (unit j A K) ≫
  (closedIso h hc j ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).obj F)
    ((etaleRestrictionSheaf j (ModuleCat.{u + 1} A)).obj K)).inv ≫
  (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).map
    (NoncommLocalHom.precomp h hc X
      ((etaleExtensionByZero_adjunction j (ModuleCat.{u + 1} R)).unit.app F))

/-- The genuine j!⊣j* adjunction proves THIS map invertible locally on Y.
It does not assert that j_* or Rj_* has no boundary contribution. -/
instance comparison_isIso : IsIso (comparison h hc j F K) := by sorry

def iso :
    NoncommLocalHom.obj h hc Y ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).obj F) K ≅
    (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).obj
      (NoncommLocalHom.obj h hc X F ((etaleRestrictionSheaf j (ModuleCat.{u + 1} A)).obj K)) :=
  @asIso _ _ _ _ (comparison h hc j F K) (comparison_isIso h hc j F K)

variable {F K}
theorem naturality {F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    {K' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} (a : F' ⟶ F) (b : K ⟶ K') :
    NoncommLocalHom.map h hc Y ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).map a) b ≫
      comparison h hc j F' K' = comparison h hc j F K ≫
    (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).map
      (NoncommLocalHom.map h hc X a ((etaleRestrictionSheaf j (ModuleCat.{u + 1} A)).map b)) := by sorry

end OpenHomRestrictionComparison
