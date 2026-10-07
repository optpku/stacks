module

public import Mathlib.Algebra.Module.Projective
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap66.«66_26_1_1_Restrict»

/-!
# Locally projective modules on algebraic spaces

A sheaf of modules on an algebraic space is locally projective when its sections over every
affine étale object are projective modules over the corresponding ring of functions. This is
the algebraic-space analogue of `Scheme.Modules.IsLocallyProjective`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The ring of functions `Γ(U, 𝒪_U)` of a scheme étale over `X`. -/
abbrev structureRing (U : smallEtaleSite X) :=
  (structureSheaf X).obj.obj (op U)

/-- The structure ring of an étale object is the global-sections ring of its underlying scheme. -/
theorem structureRing_obj (U : smallEtaleSite X) :
    structureRing U = RingCat.of Γ(U.left.left, ⊤) :=
  sorry

/-- The module of sections of `ℱ` over a scheme étale over `X`. -/
abbrev sectionModule (ℱ : X.Modules) (U : smallEtaleSite X) :=
  (SheafOfModules.evaluation (structureSheaf X) (op U)).obj ℱ

/-- Section modules are the values of the underlying presheaf of modules. -/
theorem sectionModule_val (ℱ : X.Modules) (U : smallEtaleSite X) :
    sectionModule ℱ U = ℱ.val.obj (op U) :=
  sorry

/-- A sheaf of modules on an algebraic space is locally projective when its sections over every
affine étale object are projective over the corresponding ring of functions. -/
class IsLocallyProjective (ℱ : X.Modules) : Prop where
  /-- Projectivity of sections over a chosen affine étale object. -/
  affineEtale_projective (U : affineEtaleSite X) :
    Module.Projective (structureRing U.obj) (sectionModule ℱ U.obj)

/-- Local projectivity is equivalent to affine-étale sectionwise projectivity. -/
theorem isLocallyProjective_iff (ℱ : X.Modules) :
    IsLocallyProjective ℱ ↔
      ∀ U : affineEtaleSite X,
        Module.Projective (structureRing U.obj) (sectionModule ℱ U.obj) :=
  sorry

namespace IsLocallyProjective

/-- A module sheaf whose affine-étale sections are projective is locally projective. -/
theorem of_affineEtale {ℱ : X.Modules}
    (h : ∀ U : affineEtaleSite X,
      Module.Projective (structureRing U.obj) (sectionModule ℱ U.obj)) :
    IsLocallyProjective ℱ :=
  sorry

/-- A locally projective module has projective sections over every affine étale object. -/
theorem projective_sections (ℱ : X.Modules) [IsLocallyProjective ℱ]
    (U : smallEtaleSite X) [IsAffine U.left.left] :
    Module.Projective (structureRing U) (sectionModule ℱ U) :=
  sorry

end IsLocallyProjective

/-- Projectivity of affine-étale sections is available to typeclass search from local
projectivity. -/
instance instProjectiveAffineEtale (ℱ : X.Modules) [IsLocallyProjective ℱ]
    (U : affineEtaleSite X) :
    Module.Projective (structureRing U.obj) (sectionModule ℱ U.obj) :=
  sorry

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is locally
projective. -/
instance instIsLocallyProjective_unit :
    IsLocallyProjective (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

/-- Restriction of an `𝒪_Y`-module along a morphism equipped with an explicit étaleness
witness. -/
def restrictEtale {X Y : AlgebraicSpace S} (𝒢 : Y.Modules) (f : X ⟶ Y) (hf : Etale f) :
    X.Modules :=
  @restrict S X Y 𝒢 f hf

/-- `restrictEtale` agrees with `restrict` when étaleness is available as an instance. -/
theorem restrictEtale_eq {X Y : AlgebraicSpace S} (𝒢 : Y.Modules) (f : X ⟶ Y)
    [hf : Etale f] : restrictEtale 𝒢 f hf = restrict 𝒢 f :=
  sorry

/-- Étale restriction of a locally projective quasi-coherent module remains locally projective. -/
theorem IsLocallyProjective.restrict {X Y : AlgebraicSpace S} (ℱ : Y.Modules)
    (f : X ⟶ Y) [Etale f] [ℱ.IsQuasicoherent] (hℱ : IsLocallyProjective ℱ) :
    IsLocallyProjective (restrict ℱ f) :=
  sorry

/-- A quasi-coherent module on an algebraic space is locally projective if and only if all of
its restrictions along étale morphisms from schemes are locally projective. -/
theorem isLocallyProjective_iff_forall_etale (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsLocallyProjective ℱ ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
        IsLocallyProjective (restrict ℱ φ) :=
  sorry

/-- A quasi-coherent module on an algebraic space is locally projective if and only if it
restricts to a locally projective module along some surjective étale morphism from a scheme. -/
theorem isLocallyProjective_iff_exists_surjective_etale (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] :
    IsLocallyProjective ℱ ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ),
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          IsLocallyProjective (restrictEtale ℱ φ hφ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
