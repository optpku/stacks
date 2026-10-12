/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections

/-!
# Étale-to-pro-étale comparison of small sites

The inclusion `u : X.Etale ⥤ X.ProEt` of an étale object over `X` into the
small pro-étale site, together with the induced sheaf functors `ε_*` and `ε⁻¹`.
This is the underlying functor of the comparison morphism of sites
`ε : X.ProEt ⟶ X.Etale`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u u₁ v₁

namespace AlgebraicGeometry.Scheme

/-- The inclusion of the small étale site of `X` into the small pro-étale site,
sending an étale `U / X` to the same object viewed as weakly étale. This is the
underlying functor of the comparison morphism of sites `ε`. -/
abbrev etaleToProEt (X : Scheme.{u}) : X.Etale ⥤ X.ProEt :=
  MorphismProperty.Over.changeProp X etale_le_weaklyEtale le_rfl

/-- The étale-to-pro-étale comparison functor is `Over.changeProp` along
`etale_le_weaklyEtale`. -/
theorem etaleToProEt_def (X : Scheme.{u}) :
    etaleToProEt X =
      MorphismProperty.Over.changeProp X etale_le_weaklyEtale le_rfl :=
  sorry

/-- The inclusion of small étale sites into small pro-étale sites is continuous. -/
instance etaleToProEt_isContinuous (X : Scheme.{u}) :
    Functor.IsContinuous (etaleToProEt X) X.smallEtaleTopology (ProEt.topology X) :=
  sorry

/-- The inclusion of small étale sites into small pro-étale sites is a morphism
of sites. -/
instance etaleToProEt_isMorphismOfSites (X : Scheme.{u}) :
    IsMorphismOfSites X.smallEtaleTopology (ProEt.topology X) (etaleToProEt X) :=
  sorry

/-- Direct image `ε_*` of sheaves along the étale-to-pro-étale comparison. -/
abbrev etaleToProEtSheaf (X : Scheme.{u}) (A : Type u₁) [Category.{v₁} A] :
    Sheaf (ProEt.topology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  (etaleToProEt X).sheafPushforwardContinuous A
    X.smallEtaleTopology (ProEt.topology X)

/-- Direct image along `etaleToProEt` is continuous sheaf pushforward. -/
theorem etaleToProEtSheaf_def (X : Scheme.{u}) (A : Type u₁) [Category.{v₁} A] :
    etaleToProEtSheaf X A =
      (etaleToProEt X).sheafPushforwardContinuous A
        X.smallEtaleTopology (ProEt.topology X) :=
  sorry

/-- Under the canonical Kan-extension and sheafification hypotheses, comparison
direct image is a right adjoint. -/
instance etaleToProEtSheaf_isRightAdjoint (X : Scheme.{u})
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, (etaleToProEt X).op.HasLeftKanExtension F]
    [HasWeakSheafify (ProEt.topology X) A] :
    (etaleToProEtSheaf X A).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (etaleToProEt X) A X.smallEtaleTopology (ProEt.topology X)).isRightAdjoint

/-- Inverse image `ε⁻¹` of sheaves along the étale-to-pro-étale comparison. -/
noncomputable abbrev etaleToProEtPullback (X : Scheme.{u})
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, (etaleToProEt X).op.HasLeftKanExtension F]
    [HasWeakSheafify (ProEt.topology X) A] :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf (ProEt.topology X) A :=
  (etaleToProEt X).sheafPullback A X.smallEtaleTopology (ProEt.topology X)

/-- Inverse image along `etaleToProEt` is the canonical sheaf pullback. -/
theorem etaleToProEtPullback_def (X : Scheme.{u}) (A : Type u₁) [Category.{v₁} A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, (etaleToProEt X).op.HasLeftKanExtension F]
    [HasWeakSheafify (ProEt.topology X) A] :
    etaleToProEtPullback X A =
      (etaleToProEt X).sheafPullback A X.smallEtaleTopology (ProEt.topology X) :=
  sorry

/-- The canonical adjunction `ε⁻¹ ⊣ ε_*` for the étale-to-pro-étale comparison. -/
def etaleToProEt_sheafAdjunction (X : Scheme.{u}) (A : Type u₁) [Category.{v₁} A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, (etaleToProEt X).op.HasLeftKanExtension F]
    [HasWeakSheafify (ProEt.topology X) A] :
    etaleToProEtPullback X A ⊣ etaleToProEtSheaf X A :=
  Functor.sheafAdjunctionContinuous (etaleToProEt X) A
    X.smallEtaleTopology (ProEt.topology X)

/-- Direct image `ε_*` is restriction of sections along `etaleToProEt`. -/
noncomputable def etaleToProEtSheaf_obj_obj
    (X : Scheme.{u}) (G : Sheaf (ProEt.topology X) (Type (u + 1))) (U : X.Etale) :
    ((etaleToProEtSheaf X (Type (u + 1))).obj G).obj.obj (op U) ≅
      G.obj.obj (op ((etaleToProEt X).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (etaleToProEt X) (Type (u + 1)) G U

/-- Objectwise, `ε⁻¹ F` on a weakly étale `Y / X` is isomorphic to the global
sections of `f_étale⁻¹ F` on `Y.Etale`. -/
theorem etaleToProEtPullback_obj_obj (X : Scheme.{u})
    [∀ F : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension F]
    [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt)
    [HasSheafify Y.left.smallEtaleTopology (Type (u + 1))] :
    IsIsomorphic
      (((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj (op Y))
      ((((smallMorphism Y.hom)⁻¹).obj F).obj.obj (op (Etale.globalEtale Y.left))) :=
  sorry

end AlgebraicGeometry.Scheme
