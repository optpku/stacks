/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedK0.FinitePushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
  (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  (π : X ⟶ Y) [IsFinite π.left] (k : ℤ)

/- Lemma 42.23.3 (1): finite pushforward on coherent sheaves is an exact functor. -/
@[stacks 0FDR] #check
  (AlgebraicGeometry.Scheme.Modules.FinitePushforward.cohExact π :
    RingedSpace.Coh X.left.toRingedSpace ⥤ₑ RingedSpace.Coh Y.left.toRingedSpace)

/- Lemma 42.23.3 (2): finite pushforward restricts to an exact functor on coherent sheaves
with relative support dimension at most `k`. -/
@[stacks 0FDR] #check
  (AlgebraicGeometry.Scheme.Modules.FinitePushforward.cohLEExact π δ k :
    RingedSpace.CohLE X.left.toRingedSpace (X.hom.relativeDimensionFunction δ) k ⥤ₑ
      RingedSpace.CohLE Y.left.toRingedSpace (Y.hom.relativeDimensionFunction δ) k)

/- Lemma 42.23.3 (3): finite pushforward induces a homomorphism on the `K₀` groups of the
support-dimension filtration. -/
@[stacks 0FDR] #check
  (AlgebraicGeometry.Scheme.Modules.FinitePushforward.k0_of π δ k :
    ∀ F : RingedSpace.CohLE X.left.toRingedSpace
        (X.hom.relativeDimensionFunction δ) k,
      AlgebraicGeometry.Scheme.Modules.FinitePushforward.k0 π δ k
          (AbelianK0.of F) =
        AbelianK0.of
          ((AlgebraicGeometry.Scheme.Modules.FinitePushforward.cohLE π δ k).obj F))

/- Lemma 42.23.3 (4): finite pushforward induces a homomorphism on the dimension-graded
coherent `K₀` groups. -/
@[stacks 0FDR] #check
  (AlgebraicGeometry.Scheme.Modules.FinitePushforward.gradedK0_of π δ k :
    ∀ F : RingedSpace.CohLE X.left.toRingedSpace
        (X.hom.relativeDimensionFunction δ) k,
      AlgebraicGeometry.Scheme.Modules.FinitePushforward.gradedK0 π δ k
          (AlgebraicGeometry.Scheme.Modules.GradedK0.of X.hom δ k F) =
        AlgebraicGeometry.Scheme.Modules.GradedK0.of Y.hom δ k
          ((AlgebraicGeometry.Scheme.Modules.FinitePushforward.cohLE π δ k).obj F))

/- Lemma 42.23.3 (5): the cycle-to-graded-`K₀` comparison commutes with finite pushforward. -/
@[stacks 0FDR] #check
  (AlgebraicGeometry.Scheme.Modules.FinitePushforward.toK0_naturality π δ k :
    (AlgebraicGeometry.Scheme.Modules.FinitePushforward.gradedK0 π δ k).comp
        (AlgebraicGeometry.Scheme.Modules.GradedK0.toK0 X.hom δ k) =
      (AlgebraicGeometry.Scheme.Modules.GradedK0.toK0 Y.hom δ k).comp
        (CycleGroup.mapHom π.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) k))

/- Lemma 42.23.3 (6): the graded-`K₀`-to-cycle comparison commutes with finite pushforward. -/
@[stacks 0FDR] #check
  (AlgebraicGeometry.Scheme.Modules.FinitePushforward.toCycle_naturality π δ k :
    (CycleGroup.mapHom π.left (X.hom.relativeDimensionFunction δ)
      (Y.hom.relativeDimensionFunction δ) k).comp
        (AlgebraicGeometry.Scheme.Modules.GradedK0.toCycle X.hom δ k) =
      (AlgebraicGeometry.Scheme.Modules.GradedK0.toCycle Y.hom δ k).comp
        (AlgebraicGeometry.Scheme.Modules.FinitePushforward.gradedK0 π δ k))
