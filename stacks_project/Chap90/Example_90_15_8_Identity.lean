module

public import Mathlib.CategoryTheory.Category.ULift
public import stacks_project.Chap90.Definition_90_9_1_Smooth
public import stacks_project.Chap90.Definition_90_12_1_TangentSpace
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal

/-!
# Identity cofibered category as a `FormalObject` parameter

The source-facing identity functor `𝟭 (ArtinianLocalAlgCat Λ k)` is a predeformation
category, but `FormalObject` requires a total category in `Type (u + 1)` with
`Category.{u + 1}`. `identityDown` is the Hom-universe lift already used by
`identityProjection`, and `truncationFormalObject S` is the unique formal object of
`identityDown` over a given complete local base `S`.
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
  sorry

/-- The FormalObject-capable encoding of the identity functor on `C_Λ`. -/
def identityDown : identityTotal Λ k ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down

/-- `identityDown` is `ULiftHom.down`. -/
theorem identityDown_eq : identityDown Λ k = ULiftHom.down :=
  sorry

/-- Evaluating `identityDown` on a Hom-universe lift recovers the original object of `C_Λ`. -/
theorem identityDown_obj (A : ArtinianLocalAlgCat Λ k) :
    (identityDown Λ k).obj (ULiftHom.objUp A) = A :=
  sorry

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
  sorry

/-- Successor transition of truncation stages in the Hom-universe lift. -/
noncomputable def truncationStageMap (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    truncationStage Λ k S (n + 1) ⟶ truncationStage Λ k S n :=
  (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k).map (S.truncationMap n)

/-- `truncationStageMap` is the image of `S.truncationMap n` under `ULiftHom.up`. -/
theorem truncationStageMap_eq (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    truncationStageMap Λ k S n =
      (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k).map (S.truncationMap n) :=
  sorry

/-- The unique formal object of `identityDown` over a complete local base `S`, given by the
Hom-universe lifts of the maximal-adic truncations of `S`. -/
noncomputable def truncationFormalObject (S : CompleteLocalAlgCat Λ k) :
    FormalObject (identityDown Λ k) where
  base := S
  system := Functor.ofOpSequence (truncationStageMap Λ k S)
  over_obj := sorry
  over_step := sorry

/-- The complete local base of `truncationFormalObject S` is `S`. -/
theorem truncationFormalObject_base (S : CompleteLocalAlgCat Λ k) :
    (truncationFormalObject Λ k S).base = S :=
  sorry

/-- Stage `n` of `truncationFormalObject S` lies over the `n`th truncation of `S`. -/
theorem truncationFormalObject_spec (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityDown Λ k).obj ((truncationFormalObject Λ k S).system.family n) =
        S.truncation n ∧
      (identityDown Λ k).IsHomLift (S.truncationMap n)
        ((truncationFormalObject Λ k S).system.stepMap n) :=
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
    sorry

/-- The underlying total functor of `truncationBasedFunctor` is the Hom-universe lift of
`CategoryOfElements.π (restrictedCoyoneda S)`. -/
theorem truncationBasedFunctor_eq (S : CompleteLocalAlgCat Λ k) :
    (truncationBasedFunctor Λ k S).toFunctor =
      (ULiftHom.down :
          CompleteLocalAlgCat.identityTotal S ⥤
            (CompleteLocalAlgCat.restrictedCoyoneda S).Elements) ⋙
        CategoryOfElements.π (CompleteLocalAlgCat.restrictedCoyoneda S) ⋙
        (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ identityTotal Λ k) :=
  sorry

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

end CategoryTheory.Functor
