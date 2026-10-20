/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Global sections of Čech complexes over an affine base

A module sheaf on a scheme over an affine base has a Čech complex whose pushed-forward terms
may be evaluated on the base and regarded as modules over its coordinate ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenCoverCech

/-- The Čech complex of a module sheaf over `Spec A`, evaluated on the base as a complex of
`A`-modules. -/
noncomputable def globalSectionsOverSpec
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of A)) (𝒰 : X.OpenCover) (F : X.Modules) :
    CochainComplex (ModuleCat A) ℕ :=
  let H := RingedSpace.moduleGlobalSectionsRestrictionFunctor
    (Spec (CommRingCat.of A)).toRingedSpace
      (Scheme.Hom.globalSectionsMap (𝟙 (Spec (CommRingCat.of A))))
  let hH : H.Additive :=
    show (RingedSpace.moduleGlobalSectionsFunctor
        (Spec (CommRingCat.of A)).toRingedSpace ⋙
      ModuleCat.restrictScalars
        (Scheme.Hom.globalSectionsMap (𝟙 (Spec (CommRingCat.of A))))).Additive from
      inferInstance
  let hH₀ : H.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ H hH
  (@Functor.mapHomologicalComplex ℕ _ _ _ _ _ _ H hH₀ (ComplexShape.up ℕ)).obj
    (pushforward a (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) F)

end AlgebraicGeometry.Scheme.OpenCoverCech

end
