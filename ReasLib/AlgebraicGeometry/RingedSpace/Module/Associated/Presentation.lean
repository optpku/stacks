/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Morphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point.Free
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Free
public import ReasLib.Algebra.Module.FiniteFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.HomCongr
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated module sheaves from free presentations

A presentation is expressed categorically as a cokernel of a morphism between ordinary free
modules. The comparison with free module sheaves is isolated first; the presentation theorem is
then a composition of cokernel invariance and preservation of cokernels by the associated-module
functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- The associated sheaf of an ordinary free module is the free module sheaf on the same basis. -/
@[stacks 01BH "free comparison"]
noncomputable def freeIso (alpha : R →+* X.globalSectionsRing) (I : Type u) :
    obj alpha ((ModuleCat.free R).obj I) ≅
      (SheafOfModules.free I : X.Modules) :=
  (RingedSpace.Hom.pullback (pointMap alpha)).mapIso
      (RingedPoint.Module.freeIso R I) ≪≫
    RingedSpace.Hom.pullbackFreeIso (pointMap alpha) I

/-- The free-object comparison is natural in the indexing type. -/
@[stacks 01BH "free comparison naturality"]
theorem freeIso_naturality (alpha : R →+* X.globalSectionsRing)
    {I J : Type u} (f : I ⟶ J) :
    (ModuleCat.free R ⋙ functor alpha).map f ≫ (freeIso alpha J).hom =
      (freeIso alpha I).hom ≫
        (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).map f := sorry

/-- The inverse free-object comparison is natural in the indexing type. -/
@[stacks 01BH "inverse free comparison naturality"]
theorem freeIso_inv_naturality (alpha : R →+* X.globalSectionsRing)
    {I J : Type u} (f : I ⟶ J) :
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).map f ≫
        (freeIso alpha J).inv =
      (freeIso alpha I).inv ≫
        (ModuleCat.free R ⋙ functor alpha).map f := sorry

/-- The forward free-object comparisons form a natural transformation in the indexing type. -/
@[stacks 01BH "natural free comparison"]
noncomputable def freeNatTrans (alpha : R →+* X.globalSectionsRing) :
    ModuleCat.free R ⋙ functor alpha ⟶
      SheafOfModules.freeFunctor (R := X.ringCatSheaf) where
  app I := (freeIso alpha I).hom
  naturality _ _ f := freeIso_naturality alpha f

/-- The inverse free-object comparisons form a natural transformation in the indexing type. -/
@[stacks 01BH "natural inverse free comparison"]
noncomputable def freeNatTransInv (alpha : R →+* X.globalSectionsRing) :
    SheafOfModules.freeFunctor (R := X.ringCatSheaf) ⟶
      ModuleCat.free R ⋙ functor alpha where
  app I := (freeIso alpha I).inv
  naturality _ _ f := freeIso_inv_naturality alpha f

/-- A component of the forward natural free comparison is the forward objectwise comparison. -/
@[simp, stacks 01BH "natural free comparison component"]
theorem freeNatTrans_app (alpha : R →+* X.globalSectionsRing) (I : Type u) :
    (freeNatTrans alpha).app I = (freeIso alpha I).hom := sorry

/-- A component of the inverse natural free comparison is the inverse objectwise comparison. -/
@[simp, stacks 01BH "natural inverse free comparison component"]
theorem freeNatTransInv_app (alpha : R →+* X.globalSectionsRing) (I : Type u) :
    (freeNatTransInv alpha).app I = (freeIso alpha I).inv := sorry

/-- The forward and inverse natural free comparisons compose to the identity. -/
@[simp, stacks 01BH "natural free comparison forward-inverse law"]
theorem freeNatTrans_hom_inv_id (alpha : R →+* X.globalSectionsRing) :
    freeNatTrans alpha ≫ freeNatTransInv alpha = 𝟙 _ := sorry

/-- The inverse and forward natural free comparisons compose to the identity. -/
@[simp, stacks 01BH "natural free comparison inverse-forward law"]
theorem freeNatTrans_inv_hom_id (alpha : R →+* X.globalSectionsRing) :
    freeNatTransInv alpha ≫ freeNatTrans alpha = 𝟙 _ := sorry

/-- The associated-module functor sends the ordinary free-module functor to the free
module-sheaf functor. -/
@[stacks 01BH "natural free comparison"]
noncomputable def freeNatIso (alpha : R →+* X.globalSectionsRing) :
    ModuleCat.free R ⋙ functor alpha ≅
      SheafOfModules.freeFunctor (R := X.ringCatSheaf) where
  hom := freeNatTrans alpha
  inv := freeNatTransInv alpha
  hom_inv_id := freeNatTrans_hom_inv_id alpha
  inv_hom_id := freeNatTrans_inv_hom_id alpha

/-- The forward natural transformation of the natural free comparison is `freeNatTrans`. -/
@[simp, stacks 01BH "natural free comparison hom"]
theorem freeNatIso_hom (alpha : R →+* X.globalSectionsRing) :
    (freeNatIso alpha).hom = freeNatTrans alpha := sorry

/-- The inverse natural transformation of the natural free comparison is `freeNatTransInv`. -/
@[simp, stacks 01BH "natural free comparison inverse"]
theorem freeNatIso_inv (alpha : R →+* X.globalSectionsRing) :
    (freeNatIso alpha).inv = freeNatTransInv alpha := sorry

/-- The component of the natural free comparison is the objectwise free comparison. -/
@[simp, stacks 01BH "natural free comparison isomorphism component"]
theorem freeNatIso_app (alpha : R →+* X.globalSectionsRing) (I : Type u) :
    (freeNatIso alpha).app I = freeIso alpha I := sorry

/-- The forward component of the natural free comparison is the forward objectwise
comparison. -/
@[simp, stacks 01BH "natural free comparison hom component"]
theorem freeNatIso_hom_app (alpha : R →+* X.globalSectionsRing) (I : Type u) :
    (freeNatIso alpha).hom.app I = (freeIso alpha I).hom := sorry

/-- The inverse component of the natural free comparison is the inverse objectwise
comparison. -/
@[simp, stacks 01BH "natural free comparison inverse component"]
theorem freeNatIso_inv_app (alpha : R →+* X.globalSectionsRing) (I : Type u) :
    (freeNatIso alpha).inv.app I = (freeIso alpha I).inv := sorry

/-- On a finite basis, the ordinary-function model of a free module has the expected associated
free module sheaf. -/
@[stacks 01BH "finite function free comparison"]
noncomputable def functionFreeIso (alpha : R →+* X.globalSectionsRing)
    (I : Type u) [Finite I] :
    obj alpha (ModuleCat.of R (I → R)) ≅
      (SheafOfModules.free I : X.Modules) :=
  (functor alpha).mapIso (ModuleCat.funToFinsuppIso (R := R) (I := I)) ≪≫
    freeIso alpha I

/-- The function-model free module on `Fin n` corresponds to the free module sheaf on the same
basis lifted to the ambient universe. -/
@[stacks 01BH "finite function free comparison with lifted basis"]
noncomputable def finFunctionFreeIso (alpha : R →+* X.globalSectionsRing) (n : ℕ) :
    obj alpha (ModuleCat.of R (Fin n → R)) ≅
      (SheafOfModules.freeFin n : X.Modules) :=
  (functor alpha).mapIso (ModuleCat.finFunctionToUliftFinsuppIso (R := R) n) ≪≫
    freeIso alpha (ULift.{u} (Fin n))

namespace Presentation

/-- Transport of morphisms between associated free modules to morphisms between the
corresponding free module sheaves. -/
@[stacks 01BH "free morphism equivalence", stacks 01BL "free morphism equivalence"]
noncomputable def homEquiv (alpha : R →+* X.globalSectionsRing) (I J : Type u) :
    (obj alpha ((ModuleCat.free R).obj I) ⟶
        obj alpha ((ModuleCat.free R).obj J)) ≃
      ((SheafOfModules.free I : X.Modules) ⟶ SheafOfModules.free J) :=
  (freeIso alpha I).homCongr (freeIso alpha J)

/-- Forward transport across `homEquiv` is conjugation by the free comparisons. -/
@[simp]
theorem homEquiv_apply (alpha : R →+* X.globalSectionsRing) (I J : Type u)
    (f : obj alpha ((ModuleCat.free R).obj I) ⟶
      obj alpha ((ModuleCat.free R).obj J)) :
    homEquiv alpha I J f =
      (freeIso alpha I).inv ≫ f ≫ (freeIso alpha J).hom := sorry

/-- Inverse transport across `homEquiv` is conjugation by the inverse free comparisons. -/
@[simp]
theorem homEquiv_symm_apply (alpha : R →+* X.globalSectionsRing) (I J : Type u)
    (f : (SheafOfModules.free I : X.Modules) ⟶ SheafOfModules.free J) :
    (homEquiv alpha I J).symm f =
      (freeIso alpha I).hom ≫ f ≫ (freeIso alpha J).inv := sorry

/-- A morphism between free module sheaves, transported to the corresponding associated free
modules through `freeIso`. -/
@[stacks 01BL "free morphism comparison"]
noncomputable def toAssociated (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (SheafOfModules.free I : X.Modules) ⟶ SheafOfModules.free J) :
    obj alpha ((ModuleCat.free R).obj I) ⟶
      obj alpha ((ModuleCat.free R).obj J) :=
  (homEquiv alpha I J).symm f

/-- Applying `homEquiv` after transporting a free-sheaf morphism to associated modules recovers
the original morphism. -/
@[simp]
theorem homEquiv_toAssociated (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (SheafOfModules.free I : X.Modules) ⟶ SheafOfModules.free J) :
    homEquiv alpha I J (toAssociated alpha f) = f := sorry

/-- Transporting a morphism obtained from `homEquiv` back to associated modules recovers the
original morphism. -/
@[simp]
theorem toAssociated_homEquiv (alpha : R →+* X.globalSectionsRing) (I J : Type u)
    (f : obj alpha ((ModuleCat.free R).obj I) ⟶
      obj alpha ((ModuleCat.free R).obj J)) :
    toAssociated alpha (homEquiv alpha I J f) = f := sorry

/-- The morphism of free module sheaves induced by a morphism between ordinary free modules. -/
@[stacks 01BH "presentation map"]
noncomputable def map (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (ModuleCat.free R).obj J ⟶ (ModuleCat.free R).obj I) :
    (SheafOfModules.free J : X.Modules) ⟶
      (SheafOfModules.free I : X.Modules) :=
  homEquiv alpha J I ((functor alpha).map f)

namespace toAssociated

/-- Transporting a presentation map back to associated free modules recovers the functorial
image of the original module map. -/
@[stacks 01BL "free morphism compatibility"]
theorem map (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (ModuleCat.free R).obj I ⟶ (ModuleCat.free R).obj J) :
    toAssociated alpha (Presentation.map alpha f) =
      (Associated.functor alpha).map f := sorry

/-- A free-sheaf morphism comes from a free-module morphism exactly when its associated
conjugate has a preimage under the associated functor. -/
@[stacks 01BL "free morphism characterization"]
theorem isInduced_iff (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (SheafOfModules.free I : X.Modules) ⟶ SheafOfModules.free J) :
    Morphism.IsInduced alpha (toAssociated alpha f) ↔
      ∃ g : (ModuleCat.free R).obj I ⟶ (ModuleCat.free R).obj J,
        Presentation.map alpha g = f := sorry

end toAssociated

/-- The presentation map commutes with the comparison from free sheaves to associated sheaves. -/
theorem map_comp_freeIso_inv (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (ModuleCat.free R).obj J ⟶ (ModuleCat.free R).obj I) :
    map alpha f ≫ (freeIso alpha I).inv =
      (freeIso alpha J).inv ≫ (functor alpha).map f := sorry

/-- The module sheaf presented as the cokernel of a map between free module sheaves. -/
@[stacks 01BH "presentation cokernel"]
noncomputable def cokernelObj (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (ModuleCat.free R).obj J ⟶ (ModuleCat.free R).obj I) : X.Modules :=
  cokernel (map alpha f)

/-- Replacing the free module sheaves by their associated free modules does not change the
cokernel of a presentation map. -/
noncomputable def cokernelMapIso (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    (f : (ModuleCat.free R).obj J ⟶ (ModuleCat.free R).obj I) :
    cokernelObj alpha f ≅ cokernel ((functor alpha).map f) :=
  cokernel.mapIso (f := map alpha f) ((functor alpha).map f) (freeIso alpha J).symm
    (freeIso alpha I).symm (map_comp_freeIso_inv alpha f)

/-- Lemma 17.10.5 (1) (01BH): the cokernel sheaf obtained from any chosen free presentation of
`M` is canonically isomorphic to the sheaf associated to `M`. -/
@[stacks 01BH "(1)"]
noncomputable def iso (alpha : R →+* X.globalSectionsRing) {I J : Type u}
    {M : ModuleCat.{u} R}
    (f : (ModuleCat.free R).obj J ⟶ (ModuleCat.free R).obj I)
    (g : (ModuleCat.free R).obj I ⟶ M) (H : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ g H)) :
    cokernelObj alpha f ≅ obj alpha M :=
  cokernelMapIso alpha f ≪≫
    (PreservesCokernel.iso (functor alpha) f).symm ≪≫
      (functor alpha).mapIso
        (h.coconePointUniqueUpToIso (colimit.isColimit (parallelPair f 0))).symm

end Presentation

end AlgebraicGeometry.RingedSpace.Module.Associated
