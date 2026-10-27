/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.InternalHom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange.Properties

/-! # Quasi-coherent internal Hom from a finitely presented module -/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The étale restriction of a quasi-coherent fppf module is locally quasi-coherent. -/
instance restriction_isLocallyQuasiCoherent (G : QCoh X) :
    IsLocallyQuasiCoherent ((restriction X).obj G.obj) :=
  (QCoh.toLQCohFbc_mapsTo X G).1

/-- The étale restriction of a quasi-coherent fppf module has flat base change. -/
instance restriction_hasFlatBaseChange (G : QCoh X) :
    HasFlatBaseChange ((restriction X).obj G.obj) :=
  (QCoh.toLQCohFbc_mapsTo X G).2

/-- Internal Hom from a finitely presented fppf module into a quasi-coherent module
is locally quasi-coherent and has flat base change on the étale site. -/
theorem moduleSheafHomOnEtale_mem_lqcohFbc (F : fppfModules X) (G : QCoh X)
    [F.IsFinitePresentation] :
    lqcohFbc X (moduleSheafHomEtale ((restriction X).obj F)
      ((restriction X).obj G.obj)) := sorry

/-- The common internal Hom, regarded as a locally quasi-coherent module with flat base change. -/
def moduleSheafHomLQCohFbc (F : fppfModules X) (G : QCoh X)
    [F.IsFinitePresentation] : LQCohFbc X :=
  ⟨moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G.obj),
    moduleSheafHomOnEtale_mem_lqcohFbc F G⟩

/-- Forgetting the two properties of the common internal Hom recovers its étale sheaf. -/
theorem moduleSheafHomLQCohFbc_eq (F : fppfModules X) (G : QCoh X)
    [F.IsFinitePresentation] :
    (LQCohFbc.inclusion X).obj (moduleSheafHomLQCohFbc F G) =
      moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G.obj) := rfl

namespace QCoh

/-- The quasi-coherent coreflection of internal Hom from a finitely presented module. -/
def internalHomFP (F : fppfModules X) (G : QCoh X) [F.IsFinitePresentation] : QCoh X :=
  (LQCohFbc.toQCoh X).obj (moduleSheafHomLQCohFbc F G)

/-- The quasi-coherent internal Hom is the coreflector image of the common internal Hom. -/
theorem internalHomFP_eq (F : fppfModules X) (G : QCoh X) [F.IsFinitePresentation] :
    internalHomFP F G = (LQCohFbc.toQCoh X).obj (moduleSheafHomLQCohFbc F G) := rfl

/-- Morphisms into quasi-coherent internal Hom correspond to tensor morphisms on the étale site. -/
def internalHomFP_homEquiv (F : fppfModules X) (G H : QCoh X)
    [F.IsFinitePresentation] :
    (H ⟶ internalHomFP F G) ≃
      (moduleTensorEtale ((restriction X).obj H.obj) ((restriction X).obj F) ⟶
        (restriction X).obj G.obj) :=
  (((toLQCohFbcAdjunction X).homEquiv H (moduleSheafHomLQCohFbc F G)).symm.trans
    (lqcohFbc X).fullyFaithfulι.homEquiv).trans
      (moduleSheafHomOnEtale_homEquiv ((restriction X).obj F)
        ((restriction X).obj G.obj) ((restriction X).obj H.obj))

/-- Étale currying for quasi-coherent internal Hom is the composite of coreflection and currying. -/
theorem internalHomFP_homEquiv_eq (F : fppfModules X) (G H : QCoh X)
    [F.IsFinitePresentation] :
    internalHomFP_homEquiv F G H =
      (((toLQCohFbcAdjunction X).homEquiv H (moduleSheafHomLQCohFbc F G)).symm.trans
        (lqcohFbc X).fullyFaithfulι.homEquiv).trans
          (moduleSheafHomOnEtale_homEquiv ((restriction X).obj F)
            ((restriction X).obj G.obj) ((restriction X).obj H.obj)) := rfl

/-- Quasi-coherent internal Hom represents tensor morphisms of fppf modules. -/
def internalHomFP_fppfHomEquiv (F : fppfModules X) (G H : QCoh X)
    [F.IsFinitePresentation] :
    (H ⟶ internalHomFP F G) ≃ (moduleTensorFppf H.obj F ⟶ G.obj) :=
  ((((toLQCohFbcAdjunction X).homEquiv H (moduleSheafHomLQCohFbc F G)).symm.trans
    (lqcohFbc X).fullyFaithfulι.homEquiv).trans
      ((Iso.refl ((restriction X).obj H.obj)).homCongr
        (moduleSheafHom_restrictionIso F G.obj).symm)).trans
    ((restrictionHomEquiv H.obj (moduleSheafHomFppf F G.obj)).symm.trans
      (moduleSheafHomFppf_homEquiv F G.obj H.obj))

/-- The fppf tensor/internal-Hom equivalence is natural in the quasi-coherent test module. -/
theorem internalHomFP_fppfHomEquiv_naturality (F : fppfModules X)
    (G H H' : QCoh X) [F.IsFinitePresentation] (h : H' ⟶ H)
    (f : H ⟶ internalHomFP F G) :
    internalHomFP_fppfHomEquiv F G H' (h ≫ f) =
      moduleTensorFppfMap h.hom (𝟙 F) ≫ internalHomFP_fppfHomEquiv F G H f := sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
