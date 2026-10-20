/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor

/-!
# Identity categories and their formal truncation objects

The Hom-universe lift of the identity category has singleton tangent space and
satisfies Schlessinger's conditions. A complete local algebra defines a formal
object through its maximal-adic truncations and a representing based functor.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

namespace ArtinianLocalAlgCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Hom-universe lift of `C_Λ`, matching the universe constraint of `FormalObject`. -/
abbrev identityTotal : Type (u + 1) :=
  ULiftHom.{u + 1} (ArtinianLocalAlgCat Λ k)

/-- `identityTotal` is the Hom-universe lift of `ArtinianLocalAlgCat Λ k`. -/
theorem identityTotal_eq :
    identityTotal Λ k = ULiftHom.{u + 1} (ArtinianLocalAlgCat Λ k) :=
  rfl

/-- The projection forgetting the Hom-universe lift of Artinian local algebras. -/
def identityDown : identityTotal Λ k ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down

/-- `identityDown` is `ULiftHom.down`. -/
theorem identityDown_eq : identityDown Λ k = ULiftHom.down :=
  rfl

/-- Evaluating `identityDown` on a Hom-universe lift recovers the original object of `C_Λ`. -/
theorem identityDown_obj (A : ArtinianLocalAlgCat Λ k) :
    (identityDown Λ k).obj (ULiftHom.objUp A) = A :=
  rfl

/-- `identityDown` is a predeformation category. -/
instance instIsPredeformationCategory_identityDown :
    Functor.IsPredeformationCategory (identityDown Λ k) :=
  sorry

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_identityDown_op :
    Functor.IsFibered.InGroupoids (identityDown Λ k).op :=
  Functor.IsPredeformationCategory.isCofiberedInGroupoids

/-- `identityDown` is a smooth category cofibered in groupoids. -/
instance instIsSmooth_identityDown : Functor.IsSmooth (identityDown Λ k) :=
  sorry

/-- Stage `n` of the truncation formal object, as a Hom-universe lift of `S.truncation n`. -/
noncomputable def truncationStage (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityTotal Λ k :=
  ULiftHom.objUp (S.truncation n)

/-- `truncationStage S n` is the Hom-universe lift of the `n`th truncation of `S`. -/
theorem truncationStage_eq (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    truncationStage Λ k S n = ULiftHom.objUp (S.truncation n) :=
  rfl

/-- Successor transition of truncation stages in the Hom-universe lift. -/
noncomputable def truncationStageMap (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    truncationStage Λ k S (n + 1) ⟶ truncationStage Λ k S n :=
  (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k).map (S.truncationMap n)

/-- `truncationStageMap` is the image of `S.truncationMap n` under `ULiftHom.up`. -/
theorem truncationStageMap_eq (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    truncationStageMap Λ k S n =
      (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k).map (S.truncationMap n) :=
  rfl

/-- Lifted successor maps lie over the canonical maximal-adic truncation projections. -/
theorem truncationStageMap_isHomLift (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityDown Λ k).IsHomLift (S.truncationMap n) (truncationStageMap Λ k S n) :=
  sorry

/-- The formal object given by the lifted maximal-adic truncations of a complete local algebra. -/
noncomputable def truncationFormalObject (S : CompleteLocalAlgCat Λ k) :
    FormalObject (identityDown Λ k) :=
  FormalObject.of S (truncationStage Λ k S) (truncationStageMap Λ k S)
    (fun _ ↦ rfl) (truncationStageMap_isHomLift Λ k S)

/-- The complete local base of `truncationFormalObject S` is `S`. -/
theorem truncationFormalObject_base (S : CompleteLocalAlgCat Λ k) :
    (truncationFormalObject Λ k S).base = S :=
  rfl

/-- Stage `n` of `truncationFormalObject S` lies over the `n`th truncation of `S`. -/
theorem truncationFormalObject_spec (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityDown Λ k).obj ((truncationFormalObject Λ k S).system.family n) =
        S.truncation n ∧
      (identityDown Λ k).IsHomLift (S.truncationMap n)
        ((truncationFormalObject Λ k S).system.stepMap n) :=
  ⟨(truncationFormalObject Λ k S).over_obj n,
    (truncationFormalObject Λ k S).over_step n⟩

/-- The lifted category-of-elements projection commutes with the base projections. -/
theorem truncationBasedFunctor_over (S : CompleteLocalAlgCat Λ k) :
    ((ULiftHom.down :
        CompleteLocalAlgCat.identityTotal S ⥤
          (CompleteLocalAlgCat.restrictedCoyoneda S).Elements) ⋙
      CategoryOfElements.π (CompleteLocalAlgCat.restrictedCoyoneda S) ⋙
      (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k)) ⋙
        identityDown Λ k = CompleteLocalAlgCat.identityProjection S :=
  sorry

/-- The based functor `underline S |_{C_Λ} ⟶ identityDown` sending identity truncations of `S`
to truncation stages. -/
noncomputable def truncationBasedFunctor (S : CompleteLocalAlgCat Λ k) :
    BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection S) ⥤ᵇ
      BasedCategory.ofFunctor (identityDown Λ k) :=
  BasedFunctor.ofFunctor
    ((ULiftHom.down :
        CompleteLocalAlgCat.identityTotal S ⥤
          (CompleteLocalAlgCat.restrictedCoyoneda S).Elements) ⋙
      CategoryOfElements.π (CompleteLocalAlgCat.restrictedCoyoneda S) ⋙
      (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k))
    (truncationBasedFunctor_over Λ k S)

/-- The underlying total functor of `truncationBasedFunctor` is the Hom-universe lift of
`CategoryOfElements.π (restrictedCoyoneda S)`. -/
theorem truncationBasedFunctor_eq (S : CompleteLocalAlgCat Λ k) :
    (truncationBasedFunctor Λ k S).toFunctor =
      (ULiftHom.down :
          CompleteLocalAlgCat.identityTotal S ⥤
            (CompleteLocalAlgCat.restrictedCoyoneda S).Elements) ⋙
        CategoryOfElements.π (CompleteLocalAlgCat.restrictedCoyoneda S) ⋙
        (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k) :=
  rfl

/-- `truncationBasedFunctor S` represents `truncationFormalObject S`. -/
theorem truncationBasedFunctor_represents (S : CompleteLocalAlgCat Λ k) :
    FormalObject.Represents (truncationFormalObject Λ k S)
      (truncationBasedFunctor Λ k S) :=
  sorry

/-- Every formal object of `identityDown` is isomorphic to the truncation formal object of
its complete local base. -/
theorem nonempty_iso_truncationFormalObject (ξ : FormalObject (identityDown Λ k)) :
    Nonempty (ξ ≅ truncationFormalObject Λ k ξ.base) :=
  sorry

end ArtinianLocalAlgCat

namespace CategoryTheory.Functor

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The tangent space of `identityDown` is a singleton. -/
noncomputable instance instUnique_tangentSpace_identityDown :
    Unique (tangentSpace (ArtinianLocalAlgCat.identityDown Λ k)) where
  default :=
    tangentSpace.mk (ArtinianLocalAlgCat.identityDown Λ k)
      (Fiber.mk (ArtinianLocalAlgCat.identityDown_obj Λ k
        (ArtinianLocalAlgCat.dualNumber Λ k)))
  uniq := sorry

/-- The tangent space of the identity functor on Artinian local algebras is a singleton. -/
noncomputable instance instUnique_tangentSpace_id :
    Unique (tangentSpace (𝟭 (ArtinianLocalAlgCat Λ k))) where
  default :=
    tangentSpace.mk (𝟭 (ArtinianLocalAlgCat Λ k))
      ⟨ArtinianLocalAlgCat.dualNumber Λ k, rfl⟩
  uniq := sorry

/-- The lifted identity projection satisfies Schlessinger's condition (S1). -/
instance instHasSchlessingerS1_identityDown :
    HasSchlessingerS1 (ArtinianLocalAlgCat.identityDown Λ k) :=
  sorry

/-- The lifted identity projection satisfies Schlessinger's condition (S2). -/
instance instHasSchlessingerS2_identityDown :
    HasSchlessingerS2 (ArtinianLocalAlgCat.identityDown Λ k) :=
  sorry

/-- The canonical tangent module of the lifted identity projection is finite-dimensional. -/
noncomputable instance instFiniteDimensional_tangentSpace_identityDown :
    FiniteDimensional k
      ((fiberIsoClassFunctor (ArtinianLocalAlgCat.identityDown Λ k)).obj
        (ArtinianLocalAlgCat.dualNumber Λ k)) :=
  sorry

end CategoryTheory.Functor
