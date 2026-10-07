module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import stacks_project.Chap109.Definition_109_22_2_Spaces
public import stacks_project.Chap109.Lemma_109_18_1_Substack

/-!
# Stable curves

There is an open substack 𝒞urves^{stable} ⊂ 𝒞urves classifying stable
families of curves, equivalently proper schemes over a field whose
singularities are at-worst-nodal, of dimension 1, with H⁰(X, 𝒪_X) = k,
genus at least 2 and no rational tails or bridges, equivalently the same
nodal, dimension and global-sections conditions with ω_X ample.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.22.3 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{stable}` if and only if
`X ⟶ S` is a stable family of curves. -/
@[stacks 0E76]
theorem classifying_factorsThrough_stable_iff
    {S : Scheme.{u}} (P : Obj S) :
    stable S P ↔ AlgebraicSpace.IsStableFamily (hom P) :=
  sorry

/-- Lemma 109.22.3 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{stable}` if and only if the singularities of `X` are
at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is at least
two, and `X` has no rational tails or bridges. -/
@[stacks 0E76]
theorem classifying_factorsThrough_stable_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    stable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          2 ≤ SchemeOverField.genus X hdim1 hΓ ∧
            ¬ Nonempty (SchemeOverField.RationalTail X) ∧
            ¬ Nonempty (RationalBridge X) :=
  sorry

/-- Lemma 109.22.3 (3): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{stable}` if and only if the singularities of `X` are
at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, and `ω_X` is ample. -/
@[stacks 0E76]
theorem classifying_factorsThrough_stable_iff_scheme_dualizing
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    stable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        Scheme.Modules.isAmpleObject (dualizingModule X.hom) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
