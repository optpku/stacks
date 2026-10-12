/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_24_2_Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine comparison for the cotangent complex of a scheme morphism

Lemma 92.24.2: the canonical map `tilde(L_{B/A}) ⟶ L_{X/Y}|_U` is an isomorphism
in `D(O_U)`, and is compatible with restriction to smaller affine opens.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CotangentComplex

/-- Lemma 92.24.2 (1). Let `f : X ⟶ Y` be a morphism of schemes. Let `U = Spec B ⊆ X`
and `V = Spec A ⊆ Y` be affine opens such that `f(U) ⊆ V`. The canonical map of
complexes `tilde(L_{B/A}) ⟶ L_{X/Y}|_U` is an isomorphism in `D(O_U)`. -/
@[stacks 08T3]
theorem affineComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) :
    IsIso (DerivedCategory.Q.map (affineComparison f hU e)) :=
  sorry

/-- Lemma 92.24.2 (2). The canonical affine comparison of cotangent complexes is
compatible with restriction to smaller affine opens of `X` and `Y`. -/
@[stacks 08T3]
theorem affineComparison_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : X.Opens} {V V' : Y.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hUU' : U' ≤ U) (hVV' : V' ≤ V)
    (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V') :
    affineComparisonPullbackIso hUU'
          (RingHom.cotangentComplex (f.sectionsMapAlong V U e)) ≫
        ((tilde.functor (CommRingCat.of Γ(X, U'))).mapHomologicalComplex (up ℤ)).map
          (Algebra.CotangentComplex.map (f.sectionsMapAlong V U e)
            (f.sectionsMapAlong V' U' e')
            (Y.presheaf.map (homOfLE hVV').op).hom
            (X.presheaf.map (homOfLE hUU').op).hom
            (sectionsMapAlong_restrict_square f hUU' hVV' e e')) ≫
        affineComparison f hU' e' =
      ((Modules.pullback
            (Spec.map (X.presheaf.map (homOfLE hUU').op))).mapHomologicalComplex
          (up ℤ)).map
          (affineComparison f hU e) ≫
        nestedAffinePullbackIso_map hU hU' hUU' (cotangentComplex f) :=
  sorry

end CotangentComplex
end AlgebraicGeometry.Scheme.Hom
