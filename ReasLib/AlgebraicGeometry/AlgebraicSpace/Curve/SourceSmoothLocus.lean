/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverCoefficient
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory

/-!
# Relative smooth source locus of the stack of curves

The relative smooth source locus over a scheme consists of families whose
classifying morphism factors through an open on which the stack's structure
morphism is smooth. Over a flat coefficient base, the deformation category of
a proper scheme of dimension at most one detects membership in this locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty Functor
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose classifying morphism
factors through an open substack of `𝒞urves` on which the structure morphism
`toIdentitySlice (toGroupoids S)` is smooth. This is the relative smooth
source locus of the stack of curves over `S`. -/
def sourceSmoothLocus (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    ∃ (U : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
      (ι : U ⟶ toGroupoids S),
      CohStack.OpenImmersion ι ∧
        CohStack.Hom.Smooth (ι ≫ CohStack.toIdentitySlice (toGroupoids S)) ∧
          ∃ (u : U.total), Nonempty (P ≅ (Groupoids.toFunctor ι).obj u)

/-- Membership in `sourceSmoothLocus` means there is an open immersion into
`toGroupoids S` along which the structure morphism is smooth, and the family
is in the essential image of that open. -/
theorem sourceSmoothLocus_iff {S : Scheme.{u}} (P : Obj S) :
    sourceSmoothLocus S P ↔
      ∃ (U : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
        (ι : U ⟶ toGroupoids S),
        CohStack.OpenImmersion ι ∧
          CohStack.Hom.Smooth
              (ι ≫ CohStack.toIdentitySlice (toGroupoids S)) ∧
            ∃ (u : U.total),
              Nonempty (P ≅ (Groupoids.toFunctor ι).obj u) :=
  Iff.rfl

/-- The smooth source locus of `𝒞urves` is closed under isomorphisms of
families. -/
instance instIsClosedUnderIsomorphisms_sourceSmoothLocus (S : Scheme.{u}) :
    (sourceSmoothLocus S).IsClosedUnderIsomorphisms :=
  sorry

/-- For a proper scheme of topological Krull dimension at most one over a field,
its coefficient-based curve family lies in the relative smooth source locus
if and only if its scheme deformation category is unobstructed. The coefficient
ring is Noetherian, the residue field is finite over it, and the coefficient
ring is flat over the integers. Under this flat base change, the relative locus
is the pullback of the smooth source locus over the integers. -/
theorem classifying_factorsThrough_sourceSmoothLocus_iff_unobstructed
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (Λ : Type u)
    [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ k] [Module.Finite Λ k]
    [Module.Flat ℤ Λ] :
    sourceSmoothLocus (Spec (CommRingCat.of Λ))
        (mkOverCoefficient X hdim Λ) ↔
      Functor.IsUnobstructed
        (Over.forget (Fiber.fiberInclusion.obj
            (FlatSchemeCat.residueObj Λ k X.left X.hom)) ⋙
          FlatSchemeCat.forget Λ k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
