module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import stacks_project.Chap109.Lemma_109_11_1_Substack

/-!
# Geometrically reduced and connected curves of dimension 1

There is an open substack `𝒞urves^{grc, 1} ⊂ 𝒞urves` classifying families of
curves with reduced, connected geometric fibres of dimension `1`, equivalently
proper geometrically reduced geometrically connected schemes of dimension `1`
over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.11.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{grc, 1}` if and only if the
geometric fibres of `X ⟶ S` are reduced, connected, and of dimension `1`. -/
@[stacks 0E1I]
theorem classifying_factorsThrough_geometricallyReducedConnectedDim1_iff
    {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1 S P ↔
      Hom.HasReducedGeometricFibres (hom P) ∧
        Hom.HasConnectedGeometricFibres (hom P) ∧
          ∀ ybar : GeometricPoint (ofOver (base P)),
            dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1 :=
  sorry

/-- Lemma 109.11.1 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{grc, 1}` if and only if `X` is geometrically reduced,
geometrically connected, and of dimension `1`. -/
@[stacks 0E1I]
theorem classifying_factorsThrough_geometricallyReducedConnectedDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    geometricallyReducedConnectedDim1 (Spec (CommRingCat.of k))
        (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.geometricallyReduced X ∧
        GeometricallyConnected X.hom ∧
          topologicalKrullDim X.left = 1 :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
