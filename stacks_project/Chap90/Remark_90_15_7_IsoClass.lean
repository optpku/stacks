/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.IsoClass

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.BasedFunctor FormalObject
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Remark 90.15.7: canonical fibre-class constructions and their computation laws. -/
#check (CategoryTheory.Functor.isoClassTotal :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op],
    Type (u + 1))

#check (CategoryTheory.Functor.isoClassTotal_eq :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op],
    isoClassTotal p = ULiftHom.{u + 1} (fiberIsoClassCopresheaf p).Elements)

#check (CategoryTheory.Functor.isoClassProjection :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op],
    isoClassTotal p ⥤ ArtinianLocalAlgCat Λ k)

#check (CategoryTheory.Functor.isoClassProjection_eq :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op],
    isoClassProjection p =
      (ULiftHom.down : isoClassTotal p ⥤ (fiberIsoClassCopresheaf p).Elements) ⋙
        CategoryOfElements.π (fiberIsoClassCopresheaf p))

#check (CategoryTheory.Functor.instIsFiberedInGroupoids_isoClassProjection_op :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op],
    IsFibered.InGroupoids (isoClassProjection p).op)

#check (CategoryTheory.Functor.instIsPredeformationCategory_isoClassProjection :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [IsPredeformationCategory p],
    IsPredeformationCategory (isoClassProjection p))

#check (CategoryTheory.BasedFunctor.toIsoClassULift_over :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    (toIsoClassFunctor p ⋙
      (ULiftHom.up :
        (Functor.fiberIsoClassCopresheaf p).Elements ⥤ Functor.isoClassTotal p)) ⋙
      Functor.isoClassProjection p = p)

#check (CategoryTheory.BasedFunctor.toIsoClassULift :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (Functor.isoClassProjection p))

#check (CategoryTheory.BasedFunctor.toIsoClassULift_obj :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (x : F),
    (toIsoClassULift p).obj x = ULiftHom.objUp ((toIsoClassFunctor p).obj x))

#check (CategoryTheory.BasedFunctor.toIsoClassULift_comp_π :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    (toIsoClassULift p).toFunctor ⋙ Functor.isoClassProjection p = p)

#check (CategoryTheory.BasedFunctor.instIsSmooth_toIsoClassULift :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    IsSmooth (toIsoClassULift p))

#check (CategoryTheory.Functor.isoClassTangentMap :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [IsPredeformationCategory p],
    tangentSpace p → tangentSpace (isoClassProjection p))

#check (CategoryTheory.Functor.isoClassTangentMap_bijective :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [IsPredeformationCategory p],
    Function.Bijective (isoClassTangentMap p))

#check (FormalObject.isoClassStage :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ),
    Functor.isoClassTotal p)

#check (FormalObject.isoClassStage_eq :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ),
    isoClassStage ξ n = (BasedFunctor.toIsoClassULift p).obj (ξ.system.family n))

#check (FormalObject.isoClassStageMap :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ),
    isoClassStage ξ (n + 1) ⟶ isoClassStage ξ n)

#check (FormalObject.isoClassStageMap_eq :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) (n : ℕ),
    isoClassStageMap ξ n = (BasedFunctor.toIsoClassULift p).map (ξ.system.stepMap n))

#check (FormalObject.isoClass_over_obj :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    (n : ℕ),
    (Functor.isoClassProjection p).obj
        (SequentialInverseSystem.family
          (ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor) n) =
      ξ.base.truncation n)

#check (FormalObject.isoClass_over_step :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    (n : ℕ),
    (Functor.isoClassProjection p).IsHomLift (ξ.base.truncationMap n)
      (SequentialInverseSystem.stepMap
        (ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor) n))

#check (FormalObject.isoClass :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p),
    FormalObject (Functor.isoClassProjection p))

#check (FormalObject.isoClass_base :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p),
    (isoClass ξ).base = ξ.base)

#check (FormalObject.isoClass_system :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p),
    (isoClass ξ).system = ξ.system ⋙ (BasedFunctor.toIsoClassULift p).toFunctor)

#check (FormalObject.isoClass_represents :
    ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ),
    Represents (isoClass ξ) (φ ⋙ BasedFunctor.toIsoClassULift p))
