/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
public import stacks_project.Chap85.Lemma_85_17_1_Equivalence

/-!
# Slice hypercovering conversion

A hypercovering of an object `X` is a site-level hypercovering of the terminal
presheaf on `C / X`. Instantiating hypercovering descent on `J.over X` yields an
equivalence between sheaves on `C / X` and cartesian sheaves on `(C / K)_total`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)

/-- The degree-`0` local-surjectivity condition for a hypercovering of `X`, viewed
on the slice site `J.over X`. -/
theorem zero_locallySurjective_slice :
    HypercoveringOf.Terminal.ZeroLocallySurjective (J.over X) K.toSimplicialObject :=
  sorry

/-- The degree-`1` local-surjectivity condition for a hypercovering of `X`, viewed
on the slice site `J.over X`. -/
theorem one_locallySurjective_slice :
    HypercoveringOf.Terminal.OneLocallySurjective (J.over X) K.toSimplicialObject :=
  sorry

/-- The higher matching-map local-surjectivity conditions for a hypercovering of
`X`, viewed on the slice site `J.over X`. -/
theorem higher_locallySurjective_slice :
    ∀ n : ℕ,
      HypercoveringOf.Terminal.HigherLocallySurjective (J.over X) K.toSimplicialObject
        (n + 1) :=
  sorry

/-- The site-level hypercovering of the terminal presheaf on `C / X` associated to a
hypercovering of an object `X`. -/
@[reducible] def toSliceTerminal : HypercoveringOf.Terminal.{w} (J.over X) where
  simplicial := K.toSimplicialObject
  augmentation := HypercoveringOf.terminalAugmentation K.toSimplicialObject
  isLocalHypercover :=
    SimplicialObject.Augmented.IsLocalHypercover.of_zero_one_higher
      (zero_locallySurjective_slice J X K) (one_locallySurjective_slice J X K)
      (higher_locallySurjective_slice J X K)

/-- The underlying simplicial object of `toSliceTerminal` is the simplicial object of
the original hypercovering of `X`. -/
theorem toSliceTerminal_simplicial :
    (toSliceTerminal J X K).simplicial = K.toSimplicialObject :=
  sorry

variable (A : Type (max w u v + 1)) [Category.{max w u v} A]
variable [HasWeakSheafify (J.over X) A]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject) A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ A,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Inverse image along `j_total` implements an equivalence between sheaves on
`C / X` and cartesian sheaves on `(C / K)_total`, with quasi-inverse the direct
image. -/
def cartesianEquivalence :
    Sheaf (J.over X) A ≌ Cartesian (J.over X) K.toSimplicialObject A :=
  SemiRepresentableFamily.cartesianEquivalence.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K) A

/-- The forward functor of `cartesianEquivalence` is `a⁻¹` corestricted to cartesian
sheaves. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence J X K A).functor =
      SemiRepresentableFamily.cartesianFunctor.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) A :=
  sorry

/-- The inverse functor of `cartesianEquivalence` is `a_*` on cartesian sheaves. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence J X K A).inverse =
      SemiRepresentableFamily.cartesianInverse.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) A :=
  sorry

/-- A sheaf on `(C / K)_total` lies in the essential image of `a⁻¹` if and only if it
is cartesian. -/
theorem mem_essImage_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject) A) :
    (inverseImage (J.over X) K.toSimplicialObject A).essImage G ↔
      IsCartesian (J.over X) K.toSimplicialObject A G :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering of an object is full. -/
instance inverseImage_full :
    (inverseImage (J.over X) K.toSimplicialObject A).Full :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering of an object is faithful. -/
instance inverseImage_faithful :
    (inverseImage (J.over X) K.toSimplicialObject A).Faithful :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering of an object is fully faithful. -/
def inverseImage_fullyFaithful :
    (inverseImage (J.over X) K.toSimplicialObject A).FullyFaithful :=
  FullyFaithful.ofFullyFaithful _

end CategoryTheory.Hypercovering
