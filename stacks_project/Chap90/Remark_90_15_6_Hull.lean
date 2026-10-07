module

public import stacks_project.Chap90.«90_15_0_1»
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal

/-!
# Hulls of formal objects

A hull is a versal formal object whose differential is bijective, i.e. the named
equation `BijectiveDifferential` of 90.15.0.1 holds. The associated cofibered set of
a set-valued functor on `ArtinianLocalAlgCat` is recorded as `elementsProjection`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Hom-universe lift of the category of elements of a set-valued functor on
`ArtinianLocalAlgCat Λ k`, matching the object/hom constraint of `FormalObject`. -/
abbrev elementsTotal (F : ArtinianLocalAlgCat Λ k ⥤ Type u) : Type (u + 1) :=
  ULiftHom.{u + 1} F.Elements

/-- `elementsTotal F` is the Hom-universe lift of `F.Elements`. -/
theorem elementsTotal_eq (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    elementsTotal F = ULiftHom.{u + 1} F.Elements := sorry

/-- Projection of the Hom-universe lift of `F.Elements` to `ArtinianLocalAlgCat Λ k`. -/
def elementsProjection (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    elementsTotal F ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : elementsTotal F ⥤ F.Elements) ⋙ CategoryOfElements.π F

/-- `elementsProjection F` is `CategoryOfElements.π F` after Hom-universe forgetful. -/
theorem elementsProjection_eq (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    elementsProjection F =
      (ULiftHom.down : elementsTotal F ⥤ F.Elements) ⋙ CategoryOfElements.π F := sorry

variable {F : Type (u + 1)} [Category.{u + 1} F]

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] : IsFibered.InGroupoids p.op := sorry

/-- The identity projection of a complete local algebra is a predeformation category. -/
instance instIsPredeformationCategory_identityProjection
    (R : CompleteLocalAlgCat Λ k) :
    IsPredeformationCategory (CompleteLocalAlgCat.identityProjection R) := sorry

end CategoryTheory.Functor

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- A hull is a versal formal object `ξ` of a predeformation category such that
`differential ξ` is bijective, i.e. `BijectiveDifferential ξ` holds. -/
class IsHull (ξ : FormalObject p) [Functor.IsPredeformationCategory p] : Prop
    extends IsVersal ξ where
  /-- The differential of `ξ` is bijective. -/
  bijective_differential : BijectiveDifferential ξ

/-- A formal object is a hull iff it is versal and satisfies `BijectiveDifferential`. -/
theorem isHull_iff (ξ : FormalObject p) [Functor.IsPredeformationCategory p] :
    IsHull ξ ↔ IsVersal ξ ∧ BijectiveDifferential ξ := sorry

/-- A hull has bijective differential. -/
theorem IsHull.spec (ξ : FormalObject p) [Functor.IsPredeformationCategory p]
    [IsHull ξ] : BijectiveDifferential ξ := sorry

end FormalObject

namespace CompleteLocalAlgCat

/-- The identity formal object of a restricted coyoneda functor is a hull. -/
instance instIsHullIdentityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject.IsHull (identityFormalObject R) := sorry

end CompleteLocalAlgCat
