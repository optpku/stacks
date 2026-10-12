/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import stacks_project.Chap109.Lemma_109_8_1_Substack
public import stacks_project.Chap109.Lemma_109_15_1_SourceSmoothLocus

/-!
# Smooth source locus of the stack of curves

For a proper scheme of dimension at most one over a field, after a flat
coefficient base change `Spec Λ ⟶ Spec(Z)`, the classifying morphism
factors through the smooth source locus of `𝒞urves ⟶ Spec(Z)` if and only
if the scheme deformation category is unobstructed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The morphism `Spec k ⟶ Spec Λ` induced by a coefficient algebra. -/
def specMapCoefficient (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of Λ) :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ k))

/-- `specMapCoefficient Λ k` is `Spec.map` of the coefficient algebra. -/
theorem specMapCoefficient_eq (Λ k : Type u) [CommRing Λ] [Field k]
    [Algebra Λ k] :
    specMapCoefficient Λ k =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) :=
  sorry

/-- The morphism of algebraic spaces over `Spec Λ` associated to a scheme over
a field, with base `Spec k ⟶ Spec Λ`. -/
def schemeOverCoefficientHom {k : Type u} [Field k] (X : SchemeOverField k)
    (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    ofOver (Over.mk (X.hom ≫ specMapCoefficient Λ k)) ⟶
      ofOver (Over.mk (specMapCoefficient Λ k)) :=
  ofOverHomMk X.hom rfl

/-- `schemeOverCoefficientHom X Λ` is `ofOverHomMk` of the structure morphism
of `X` over the coefficient base. -/
theorem schemeOverCoefficientHom_eq {k : Type u} [Field k]
    (X : SchemeOverField k) (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    schemeOverCoefficientHom X Λ = ofOverHomMk X.hom rfl :=
  sorry

/-- A proper scheme over a field remains fp-flat-proper as a morphism of
algebraic spaces over a coefficient base `Spec Λ`. -/
instance instFpFlatProper_schemeOverCoefficientHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    FpFlatProper (schemeOverCoefficientHom X Λ) :=
  sorry

/-- A proper scheme of topological Krull dimension at most one over a field has
relative dimension at most one over a coefficient base `Spec Λ`. -/
theorem relativeDimensionLE_schemeOverCoefficientHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (Λ : Type u)
    [CommRing Λ] [Algebra Λ k] :
    RelativeDimensionLE (schemeOverCoefficientHom X Λ) 1 :=
  sorry

/-- Package a proper scheme of topological Krull dimension at most one over a
field as a family of curves over `Spec Λ` with base `Spec k ⟶ Spec Λ`. -/
def mkOverCoefficient {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    Obj (Spec (CommRingCat.of Λ)) :=
  @mk (Spec (CommRingCat.of Λ)) (Over.mk (specMapCoefficient Λ k))
    (ofOver (Over.mk (X.hom ≫ specMapCoefficient Λ k)))
    (schemeOverCoefficientHom X Λ)
    (instFpFlatProper_schemeOverCoefficientHom X Λ)
    (relativeDimensionLE_schemeOverCoefficientHom X hdim Λ)

/-- The structure morphism of `mkOverCoefficient X hdim Λ` is
`schemeOverCoefficientHom X Λ`. -/
theorem mkOverCoefficient_hom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (Λ : Type u)
    [CommRing Λ] [Algebra Λ k] :
    hom (mkOverCoefficient X hdim Λ) = schemeOverCoefficientHom X Λ :=
  sorry

/-- Lemma 109.15.1: for a field `k` and a proper scheme `X` of dimension at
most one over `k`, and a coefficient ring `Λ` presenting `Def_X` on Artinian
local `Λ`-algebras with residue field `k` (for example a Cohen ring), the
classifying morphism `Spec k ⟶ 𝒞urves` factors through the open where
`𝒞urves ⟶ Spec(Z)` is smooth if and only if the deformation category
`Def_X` is unobstructed.

The coefficient ring is taken flat over `Z`, so clause (1) is membership of
the packaged family over `Spec Λ` with base `Spec k ⟶ Spec Λ` in the flat
pullback of that open, equivalently the smooth source locus of
`Λ`-`𝒞urves ⟶ Spec Λ`. -/
@[stacks 0DZU]
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

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
