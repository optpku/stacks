module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap93.Lemma_93_9_4

/-!
# Hulls and prorepresentability of isomorphism classes of scheme deformations

In Example 93.9.1, if `X` is a proper `k`-scheme and `Λ` is complete local with
residue field `k` (the classical case), the functor of isomorphism classes of
objects of `Def_X` has a hull. If in addition `Der_k(𝒪_X, 𝒪_X) = 0`, then this
functor is prorepresentable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped BasedFunctor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The identity projection of a complete local algebra is a predeformation category. -/
instance instIsPredeformationCategory_identityProjection
    (R : CompleteLocalAlgCat Λ k) :
    IsPredeformationCategory (identityProjection R) :=
  sorry

/-- The isomorphism-class functor of an identity projection satisfies (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_identityProjection
    (R : CompleteLocalAlgCat Λ k) :
    HasSchlessingerH2 (fiberIsoClassFunctor (identityProjection R)) :=
  sorry

end CompleteLocalAlgCat

namespace FlatSchemeCat

variable (X : Scheme.{u})
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]

/-- The set-valued functor sending `A` to the isomorphism classes of objects of
`Def_X(A)`. -/
abbrev isoClassFunctor : ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Λ k X hX)

/-- The value of `isoClassFunctor` at `A` is the type of isomorphism classes in the
fibre of `deformationForget` over `A`. -/
theorem isoClassFunctor_obj (A : ArtinianLocalAlgCat Λ k) :
    (isoClassFunctor Λ k X hX).obj A =
      isomorphismClasses.obj (Cat.of ((deformationForget Λ k X hX).Fiber A)) :=
  sorry

/-- Hom-universe lift of the category of elements of `isoClassFunctor`, projected
to `ArtinianLocalAlgCat`, matching the object/hom constraint of `FormalObject`. -/
abbrev isoClassElementsForget :
    ULiftHom.{u + 1} (isoClassFunctor Λ k X hX).Elements ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down :
      ULiftHom.{u + 1} (isoClassFunctor Λ k X hX).Elements ⥤
        (isoClassFunctor Λ k X hX).Elements) ⋙
    CategoryOfElements.π (isoClassFunctor Λ k X hX)

/-- `isoClassElementsForget` is `CategoryOfElements.π` after Hom-universe forgetful. -/
theorem isoClassElementsForget_eq :
    isoClassElementsForget Λ k X hX =
      (ULiftHom.down :
          ULiftHom.{u + 1} (isoClassFunctor Λ k X hX).Elements ⥤
            (isoClassFunctor Λ k X hX).Elements) ⋙
        CategoryOfElements.π (isoClassFunctor Λ k X hX) :=
  sorry

/-- The Hom-universe lift of the associated cofibered set of `isoClassFunctor` is
cofibered in groupoids. -/
instance instIsFiberedInGroupoids_isoClassElementsForget_op :
    IsFibered.InGroupoids (isoClassElementsForget Λ k X hX).op :=
  sorry

/-- The Hom-universe lift of the associated cofibered set of `isoClassFunctor` is a
predeformation category. -/
instance instIsPredeformationCategory_isoClassElementsForget :
    IsPredeformationCategory (isoClassElementsForget Λ k X hX) :=
  sorry

/-- The isomorphism-class functor of `isoClassElementsForget` satisfies (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_isoClassElementsForget :
    HasSchlessingerH2 (fiberIsoClassFunctor (isoClassElementsForget Λ k X hX)) :=
  sorry

/-- Lemma 93.9.5 (1)
In Example 93.9.1 assume `X` is a proper `k`-scheme. Assume `Λ` is a complete
local ring with residue field `k` (the classical case). Then the functor
`isoClassFunctor Λ k X hX` sending `A` to the isomorphism classes of objects of
`Def_X(A)` has a hull. -/
@[stacks 0ET5]
theorem isoClassFunctor_exists_isHull [IsProper hX] [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ ξ : FormalObject (isoClassElementsForget Λ k X hX),
      FormalObject.IsVersal ξ ∧
        ∃ φ : BasedCategory.ofFunctor
            (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
            BasedCategory.ofFunctor (isoClassElementsForget Λ k X hX),
          FormalObject.Represents ξ φ ∧ BasedFunctor.IsSmooth φ ∧
            Function.Bijective (BasedFunctor.differential φ) :=
  sorry

/-- Lemma 93.9.5 (2)
In Example 93.9.1, with the same properness and classical assumptions, if
`Der_k(𝒪_X, 𝒪_X) = 0`, recorded as `Subsingleton (derivations Λ k X hX)`, then
`isoClassFunctor Λ k X hX` is prorepresentable. -/
@[stacks 0ET5]
theorem isoClassFunctor_isProrepresentable [IsProper hX]
    [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_der : Subsingleton (derivations Λ k X hX)) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        ((CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u}) ≅
          isoClassFunctor Λ k X hX) :=
  sorry

end FlatSchemeCat
