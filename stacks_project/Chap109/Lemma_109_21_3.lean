module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import stacks_project.Chap109.Definition_109_21_2_Spaces
public import stacks_project.Chap109.Lemma_109_18_1_Substack

/-!
# Semistable curves

There is an open substack 𝒞urves^{semistable} ⊂ 𝒞urves classifying semistable
families of curves, equivalently proper schemes over a field whose
singularities are at-worst-nodal, of dimension 1, with H⁰(X, 𝒪_X) = k,
genus at least 1 and no rational tails, equivalently the same nodal,
dimension and global-sections conditions with ω_X^{⊗ m} globally generated
for all m ≥ 2.
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

/-- The dualizing module of a proper scheme over a field is invertible, and
every integral tensor power of exponent at least two is globally generated. -/
def dualizingTensorPowersGloballyGenerated {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom] : Prop :=
  ∃ (hL : Scheme.Modules.Invertible (dualizingModule X.hom)),
    ∀ (m : ℤ), 2 ≤ m →
      SheafOfModules.IsGloballyGenerated
        (@Scheme.Modules.tensorPowerInt X.left (dualizingModule X.hom) hL m)

/-- Invertibility of the dualizing module together with global generation of
every integral tensor power of exponent at least two. -/
theorem dualizingTensorPowersGloballyGenerated_iff {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom] :
    dualizingTensorPowersGloballyGenerated X ↔
      ∃ (hL : Scheme.Modules.Invertible (dualizingModule X.hom)),
        ∀ (m : ℤ), 2 ≤ m →
          SheafOfModules.IsGloballyGenerated
            (@Scheme.Modules.tensorPowerInt X.left (dualizingModule X.hom) hL m) :=
  sorry

/-- Lemma 109.21.3 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{semistable}` if and only if
`X ⟶ S` is a semistable family of curves. -/
@[stacks 0E70]
theorem classifying_factorsThrough_semistable_iff
    {S : Scheme.{u}} (P : Obj S) :
    semistable S P ↔ AlgebraicSpace.Semistable (hom P) :=
  sorry

/-- Lemma 109.21.3 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{semistable}` if and only if the singularities of `X` are
at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is at least
one, and `X` has no rational tails. -/
@[stacks 0E70]
theorem classifying_factorsThrough_semistable_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    semistable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          1 ≤ SchemeOverField.genus X hdim1 hΓ ∧
            ¬ Nonempty (SchemeOverField.RationalTail X) :=
  sorry

/-- Lemma 109.21.3 (3): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{semistable}` if and only if the singularities of `X` are
at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, and `ω_X^{⊗ m}` is globally
generated for all `m ≥ 2`. -/
@[stacks 0E70]
theorem classifying_factorsThrough_semistable_iff_scheme_dualizing
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    semistable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        dualizingTensorPowersGloballyGenerated X :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
