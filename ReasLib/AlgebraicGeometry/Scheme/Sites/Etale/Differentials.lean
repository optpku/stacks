/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CommRingedHom
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials

/-!
# Relative differentials on the small étale site

The associated étale sheaf of scheme differentials is canonically isomorphic to
the relative differentials of the induced morphism of small étale ringed sites,
compatibly with universal derivations.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open Scheme.Etale.Small
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Small

variable {X Y : Scheme.{u}}

/-- Pushforward of commutative-ring sheaves along the small étale morphism of
sites has a left adjoint, constructed by left Kan extension and sheafification. -/
instance commRingedHom_sheafPushforwardContinuous_isRightAdjoint (f : X ⟶ Y) :
    ((commRingedHom f).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (smallCommRingedSite .etale Y).siteTopology
      (smallCommRingedSite .etale X).siteTopology).IsRightAdjoint :=
  (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (commRingedHom f).base CommRingCat.{u + 1}
    (smallCommRingedSite .etale Y).siteTopology
    (smallCommRingedSite .etale X).siteTopology).isRightAdjoint

/-- An étale object over a scheme induces the canonical pullback comparison
from the scheme's relative differentials to the object's relative differentials. -/
noncomputable def etaleComparison (f : X ⟶ Y) (U : X.Etale) :
    (RingedSpace.Hom.pullback U.hom.toShHom).obj Ω[f.toShHom] ⟶
      Ω[(U.hom ≫ f).toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    ((⟨(Category.comp_id (U.hom ≫ f)).symm⟩ :
      CommSq U.hom (U.hom ≫ f) f (𝟙 Y)).map
        (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace))

/-- Global sections of the canonical pullback comparison of relative
differentials at an étale object. -/
noncomputable def etaleComparisonSections (f : X ⟶ Y) (U : X.Etale) :
    (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).obj
        ((RingedSpace.Hom.pullback U.hom.toShHom).obj Ω[f.toShHom]) ⟶
      (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).obj
        Ω[(U.hom ≫ f).toShHom] :=
  (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).map
    (etaleComparison f U)

/-- For a morphism of schemes, there is a unique isomorphism from the relative
differentials on the small étale site to the associated sheaf of scheme
differentials whose sections match the universal differentials under the
canonical pullback comparison on every étale object. -/
theorem existsUnique_associatedModuleIso (f : X ⟶ Y) :
    ∃! e : RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f) ≅
      StandardSmall.comm .etale X (Ω[f.toShHom]),
      ∀ (U : X.Etaleᵒᵖ)
        (t : (StandardSmall.commStructureSheaf .etale X).obj.obj U),
        etaleComparisonSections f U.unop
          (ULift.down (e.hom.val.app U
            ((RingedSite.Hom.relativeDifferential (commRingedHom f)).d t))) =
          (d[(U.unop.hom ≫ f).toShHom]).d (ULift.down t) := sorry

end AlgebraicGeometry.Scheme.Etale.Small
