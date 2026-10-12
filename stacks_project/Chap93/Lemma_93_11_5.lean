/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap93.Lemma_93_11_4

/-!
# Hull and prorepresentability of isomorphism classes of algebraic space deformations

In Example 93.11.1, if `X` is a proper algebraic space over `k` and `Λ` is complete
local with residue field `k` (the classical case), the functor of isomorphism classes
of objects of `Def_X` has a hull. If in addition `Der_k(𝒪_X, 𝒪_X) = 0`, then this
functor is prorepresentable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor
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

namespace FlatAlgebraicSpaceCat

variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

/-- The set-valued functor sending `A` to the isomorphism classes of objects of
`Def_X(A)`. -/
abbrev isoClassFunctor : ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Λ k X)

/-- The value of `isoClassFunctor` at `A` is the type of isomorphism classes in the
fibre of `deformationForget` over `A`. -/
theorem isoClassFunctor_obj (A : ArtinianLocalAlgCat Λ k) :
    (isoClassFunctor Λ k X).obj A =
      isomorphismClasses.obj (Cat.of ((deformationForget Λ k X).Fiber A)) :=
  sorry

/-- Hom-universe lift of the category of elements of `isoClassFunctor`, projected
to `ArtinianLocalAlgCat`, matching the object/hom constraint of `FormalObject`. -/
abbrev isoClassElementsForget :
    ULiftHom.{u + 1} (isoClassFunctor Λ k X).Elements ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down :
      ULiftHom.{u + 1} (isoClassFunctor Λ k X).Elements ⥤
        (isoClassFunctor Λ k X).Elements) ⋙
    CategoryOfElements.π (isoClassFunctor Λ k X)

/-- `isoClassElementsForget` is `CategoryOfElements.π` after Hom-universe forgetful. -/
theorem isoClassElementsForget_eq :
    isoClassElementsForget Λ k X =
      (ULiftHom.down :
          ULiftHom.{u + 1} (isoClassFunctor Λ k X).Elements ⥤
            (isoClassFunctor Λ k X).Elements) ⋙
        CategoryOfElements.π (isoClassFunctor Λ k X) :=
  sorry

/-- The Hom-universe lift of the associated cofibered set of `isoClassFunctor` is
cofibered in groupoids. -/
instance instIsFiberedInGroupoids_isoClassElementsForget_op :
    IsFibered.InGroupoids (isoClassElementsForget Λ k X).op :=
  sorry

/-- The Hom-universe lift of the associated cofibered set of `isoClassFunctor` is a
predeformation category. -/
instance instIsPredeformationCategory_isoClassElementsForget :
    IsPredeformationCategory (isoClassElementsForget Λ k X) :=
  sorry

/-- The isomorphism-class functor of `isoClassElementsForget` satisfies (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_isoClassElementsForget :
    HasSchlessingerH2 (fiberIsoClassFunctor (isoClassElementsForget Λ k X)) :=
  sorry

/-- Lemma 93.11.5 (1)
In Example 93.11.1 assume `X` is a proper algebraic space over `k`. Assume `Λ` is a
complete local ring with residue field `k` (the classical case). Then the functor
`isoClassFunctor Λ k X` sending `A` to the isomorphism classes of objects of
`Def_X(A)` has a hull. -/
@[stacks 0ET7]
theorem exists_isHull_isoClass [AlgebraicSpace.Proper (toBase X)]
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ ξ : FormalObject (isoClassElementsForget Λ k X),
      FormalObject.IsVersal ξ ∧
        ∃ φ : BasedCategory.ofFunctor
            (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
            BasedCategory.ofFunctor (isoClassElementsForget Λ k X),
          FormalObject.Represents ξ φ ∧ BasedFunctor.IsSmooth φ ∧
            Function.Bijective (BasedFunctor.differential φ) :=
  sorry

/-- Lemma 93.11.5 (2)
In Example 93.11.1, with the same properness and classical assumptions, if
`Der_k(𝒪_X, 𝒪_X) = 0`, then `isoClassFunctor Λ k X` is prorepresentable. -/
@[stacks 0ET7]
theorem isProrepresentable_isoClass [AlgebraicSpace.Proper (toBase X)]
    [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_der : Subsingleton (derivations Λ k X)) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          isoClassFunctor Λ k X) :=
  sorry

end FlatAlgebraicSpaceCat
