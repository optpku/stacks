/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Hull
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Existence
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.IsoClass
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber

/-!
# Hom-universe lift of fibrewise isomorphism classes

The category `overline F` associated to a cofibered groupoid
`p : F ⥤ ArtinianLocalAlgCat Λ k` is the Hom-universe lift of the category of
elements of `fiberIsoClassCopresheaf p`. The canonical based morphism
`toIsoClassULift p` is the Hom-universe lift of `toIsoClass`, and
`FormalObject.isoClass` is the image of a formal object along that morphism.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]

noncomputable section

namespace CategoryTheory.Functor

/-- Hom-universe lift of the category of elements of the fibrewise
isomorphism-class functor, matching the object/hom constraint of `FormalObject`. -/
abbrev isoClassTotal (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    Type (u + 1) :=
  ULiftHom.{u + 1} (fiberIsoClassCopresheaf p).Elements

/-- `isoClassTotal p` is the Hom-universe lift of `(fiberIsoClassCopresheaf p).Elements`. -/
theorem isoClassTotal_eq (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    isoClassTotal p = ULiftHom.{u + 1} (fiberIsoClassCopresheaf p).Elements := rfl

/-- Projection of the Hom-universe lift of fibrewise isomorphism classes to `C_Λ`. -/
def isoClassProjection (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    isoClassTotal p ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : isoClassTotal p ⥤ (fiberIsoClassCopresheaf p).Elements) ⋙
    CategoryOfElements.π (fiberIsoClassCopresheaf p)

/-- `isoClassProjection p` is `CategoryOfElements.π` after Hom-universe forgetful. -/
theorem isoClassProjection_eq (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] :
    isoClassProjection p =
      (ULiftHom.down : isoClassTotal p ⥤ (fiberIsoClassCopresheaf p).Elements) ⋙
        CategoryOfElements.π (fiberIsoClassCopresheaf p) := rfl

/-- The Hom-universe lift of the category of fibrewise isomorphism classes is cofibered
in groupoids over `C_Λ`. -/
instance instIsFiberedInGroupoids_isoClassProjection_op
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    IsFibered.InGroupoids (isoClassProjection p).op :=
  sorry

/-- If `p` is a predeformation category, then so is `isoClassProjection p`. -/
instance instIsPredeformationCategory_isoClassProjection
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [IsPredeformationCategory p] :
    IsPredeformationCategory (isoClassProjection p) :=
  sorry

end CategoryTheory.Functor

namespace CategoryTheory.BasedFunctor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]

/-- The lifted canonical fibre-class functor commutes strictly with the base projection. -/
theorem toIsoClassULift_over :
    (toIsoClassFunctor p ⋙
      (ULiftHom.up :
        (Functor.fiberIsoClassCopresheaf p).Elements ⥤ Functor.isoClassTotal p)) ⋙
      Functor.isoClassProjection p = p :=
  sorry

/-- The Hom-universe lift of `toIsoClass p`, as a based morphism
`F ⟶ overline F` over `ArtinianLocalAlgCat Λ k`. -/
def toIsoClassULift :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (Functor.isoClassProjection p) :=
  ofFunctor
    (toIsoClassFunctor p ⋙
      (ULiftHom.up :
        (Functor.fiberIsoClassCopresheaf p).Elements ⥤ Functor.isoClassTotal p))
    (toIsoClassULift_over p)

/-- On objects, `toIsoClassULift p` is `toIsoClassFunctor p` followed by `ULiftHom.objUp`. -/
theorem toIsoClassULift_obj (x : F) :
    (toIsoClassULift p).obj x = ULiftHom.objUp ((toIsoClassFunctor p).obj x) := rfl

/-- The canonical morphism `toIsoClassULift p` lies strictly over `ArtinianLocalAlgCat Λ k`. -/
theorem toIsoClassULift_comp_π :
    (toIsoClassULift p).toFunctor ⋙ Functor.isoClassProjection p = p :=
  (toIsoClassULift p).w

/-- The Hom-universe lift of `toIsoClass p` is smooth. -/
instance instIsSmooth_toIsoClassULift : IsSmooth (toIsoClassULift p) :=
  sorry

end CategoryTheory.BasedFunctor

namespace CategoryTheory.Functor

/-- The map on tangent spaces induced by `toIsoClassULift p` at the dual numbers. -/
def isoClassTangentMap (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [IsPredeformationCategory p] :
    tangentSpace p → tangentSpace (isoClassProjection p) :=
  ((BasedFunctor.toIsoClassULift p).fiberFunctor
    (ArtinianLocalAlgCat.dualNumber Λ k)).isoClassesMap

/-- The canonical morphism `F ⟶ overline F` identifies tangent spaces. -/
theorem isoClassTangentMap_bijective (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [IsPredeformationCategory p] :
    Function.Bijective (isoClassTangentMap p) :=
  sorry

end CategoryTheory.Functor

namespace FormalObject

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Stage `n` of the image of `ξ` in the Hom-universe lift of fibrewise
isomorphism classes. -/
def isoClassStage [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ) :
    Functor.isoClassTotal p :=
  (BasedFunctor.toIsoClassULift p).obj (ξ.system.family n)

/-- `isoClassStage ξ n` is the image of stage `n` of `ξ` under `toIsoClassULift p`. -/
theorem isoClassStage_eq [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ) :
    isoClassStage ξ n = (BasedFunctor.toIsoClassULift p).obj (ξ.system.family n) := rfl

/-- Successor transition of `isoClassStage`. -/
def isoClassStageMap [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ) :
    isoClassStage ξ (n + 1) ⟶ isoClassStage ξ n :=
  (BasedFunctor.toIsoClassULift p).map (ξ.system.stepMap n)

/-- `isoClassStageMap` is the image of the successor transition of `ξ` under
`toIsoClassULift p`. -/
theorem isoClassStageMap_eq [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ) :
    isoClassStageMap ξ n = (BasedFunctor.toIsoClassULift p).map (ξ.system.stepMap n) := rfl

/-- The mapped inverse-system stages lie over the original base truncations. -/
theorem isoClass_over_obj [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    (n : ℕ) :
    (Functor.isoClassProjection p).obj
        (SequentialInverseSystem.family
          (ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor) n) =
      ξ.base.truncation n :=
  sorry

/-- The mapped successor transitions lift the original base truncation maps. -/
theorem isoClass_over_step [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    (n : ℕ) :
    (Functor.isoClassProjection p).IsHomLift (ξ.base.truncationMap n)
      (SequentialInverseSystem.stepMap
        (ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor) n) :=
  sorry

/-- The image of a formal object in the Hom-universe lift of fibrewise isomorphism classes. -/
def isoClass [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) :
    FormalObject (Functor.isoClassProjection p) :=
  ⟨ξ.base, ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor,
    isoClass_over_obj ξ, isoClass_over_step ξ⟩

/-- Mapping a formal object to fibrewise isomorphism classes preserves the complete
local base. -/
theorem isoClass_base [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) :
    (isoClass ξ).base = ξ.base := rfl

/-- Mapping a formal object to fibrewise isomorphism classes whiskers its inverse
system with `toIsoClassULift p`. -/
theorem isoClass_system [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) :
    (isoClass ξ).system = ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor := rfl

/-- If `φ` represents `ξ`, then `φ ⋙ toIsoClassULift p` represents `isoClass ξ`. -/
theorem isoClass_represents [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ) :
    Represents (isoClass ξ) (φ ⋙ BasedFunctor.toIsoClassULift p) :=
  sorry

end FormalObject


variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- If a formal object satisfies `BijectiveDifferential`, then so does its image in
the category of fibrewise isomorphism classes. -/
theorem bijectiveDifferential_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) (h : BijectiveDifferential ξ) :
    BijectiveDifferential (isoClass ξ) :=
  sorry

/-- If `ξ` is a versal formal object of a predeformation category
`p`, then its image `isoClass ξ` in `isoClassProjection p` is versal. -/
instance instIsVersal_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] : IsVersal (isoClass ξ) :=
  sorry

/-- If `ξ` is a hull, then so is its image in the category of fibrewise isomorphism
classes. -/
instance instIsHull_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsHull ξ] : IsHull (isoClass ξ) :=
  sorry

/-- If `ξ` is versal and `BijectiveDifferential ξ` holds, then
`isoClass ξ` is a hull of `isoClassProjection p`. -/
theorem isHull_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] (h : BijectiveDifferential ξ) :
    IsHull (isoClass ξ) :=
  sorry

/-- A predeformation category satisfying Schlessinger's conditions with finite-dimensional
canonical tangent space has a hull after passage to fibrewise isomorphism classes,
provided the residue field is separable over the residue image. -/
theorem exists_isHull_isoClass [Functor.IsPredeformationCategory p]
    [Functor.HasSchlessingerS1 p] [Functor.HasSchlessingerS2 p]
    [FiniteDimensional k
      ((Functor.fiberIsoClassFunctor p).obj (ArtinianLocalAlgCat.dualNumber Λ k))]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ∃ ξ : FormalObject (Functor.isoClassProjection p), IsHull ξ :=
  sorry

end FormalObject

end
