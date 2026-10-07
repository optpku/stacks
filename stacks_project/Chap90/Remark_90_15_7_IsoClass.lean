module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_12_1_TangentSpace
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Remark_90_8_5_IsoClass

/-!
# Hom-universe lift of fibrewise isomorphism classes

The category `overline F` associated to a cofibered groupoid
`p : F ⥤ ArtinianLocalAlgCat Λ k` is the Hom-universe lift of the category of
elements of `fiberIsoClassFunctor p`. The canonical based morphism
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
  ULiftHom.{u + 1} (fiberIsoClassFunctor p).Elements

/-- `isoClassTotal p` is the Hom-universe lift of `(fiberIsoClassFunctor p).Elements`. -/
theorem isoClassTotal_eq (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    isoClassTotal p = ULiftHom.{u + 1} (fiberIsoClassFunctor p).Elements :=
  sorry

/-- Projection of the Hom-universe lift of fibrewise isomorphism classes to `C_Λ`. -/
def isoClassProjection (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    isoClassTotal p ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : isoClassTotal p ⥤ (fiberIsoClassFunctor p).Elements) ⋙
    CategoryOfElements.π (fiberIsoClassFunctor p)

/-- `isoClassProjection p` is `CategoryOfElements.π` after Hom-universe forgetful. -/
theorem isoClassProjection_eq (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] :
    isoClassProjection p =
      (ULiftHom.down : isoClassTotal p ⥤ (fiberIsoClassFunctor p).Elements) ⋙
        CategoryOfElements.π (fiberIsoClassFunctor p) :=
  sorry

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

/-- The Hom-universe lift of `toIsoClass p`, as a based morphism
`F ⟶ overline F` over `ArtinianLocalAlgCat Λ k`. -/
def toIsoClassULift :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (Functor.isoClassProjection p) :=
  ofFunctor
    (toIsoClassFunctor p ⋙
      (ULiftHom.up :
        (Functor.fiberIsoClassFunctor p).Elements ⥤ Functor.isoClassTotal p))
    sorry

/-- On objects, `toIsoClassULift p` is `toIsoClassFunctor p` followed by `ULiftHom.objUp`. -/
theorem toIsoClassULift_obj (x : F) :
    (toIsoClassULift p).obj x = ULiftHom.objUp ((toIsoClassFunctor p).obj x) :=
  sorry

/-- The canonical morphism `toIsoClassULift p` lies strictly over `ArtinianLocalAlgCat Λ k`. -/
theorem toIsoClassULift_comp_π :
    (toIsoClassULift p).toFunctor ⋙ Functor.isoClassProjection p = p :=
  sorry

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
    isoClassStage ξ n = (BasedFunctor.toIsoClassULift p).obj (ξ.system.family n) :=
  sorry

/-- Successor transition of `isoClassStage`. -/
def isoClassStageMap [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ) :
    isoClassStage ξ (n + 1) ⟶ isoClassStage ξ n :=
  (BasedFunctor.toIsoClassULift p).map (ξ.system.stepMap n)

/-- `isoClassStageMap` is the image of the successor transition of `ξ` under
`toIsoClassULift p`. -/
theorem isoClassStageMap_eq [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ) :
    isoClassStageMap ξ n = (BasedFunctor.toIsoClassULift p).map (ξ.system.stepMap n) :=
  sorry

/-- The image of a formal object of `p` in the Hom-universe lift of fibrewise
isomorphism classes. -/
def isoClass [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) :
    FormalObject (Functor.isoClassProjection p) where
  base := ξ.base
  system := Functor.ofOpSequence (isoClassStageMap ξ)
  over_obj := sorry
  over_step := sorry

/-- Mapping a formal object to fibrewise isomorphism classes preserves the complete
local base. -/
theorem isoClass_base [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) :
    (isoClass ξ).base = ξ.base :=
  sorry

/-- Mapping a formal object to fibrewise isomorphism classes whiskers its inverse
system with `toIsoClassULift p`. -/
theorem isoClass_system [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) :
    (isoClass ξ).system = ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor :=
  sorry

/-- If `φ` represents `ξ`, then `φ ⋙ toIsoClassULift p` represents `isoClass ξ`. -/
theorem isoClass_represents [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ) :
    Represents (isoClass ξ) (φ ⋙ BasedFunctor.toIsoClassULift p) :=
  sorry

end FormalObject

end
