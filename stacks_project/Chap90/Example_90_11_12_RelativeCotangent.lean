/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Separable
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Example_90_11_11_Derivation
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Lemma_90_4_2_Cotangent

/-!
# Relative cotangent space of an object of `Ĉ_Λ`

The relative cotangent space of `S : CompleteLocalAlgCat Λ k` is the `k`-vector
space `m_S / (m_Λ S + m_S²)`, realized as the quotient of
`CotangentSpace S.carrier` by the `k`-span of the image of
`ker (algebraMap Λ k)`. A `Λ`-derivation `S.carrier → k` restricts to a
`k`-linear form on this space, and the tangent space of
`restrictedCoyoneda S` pairs with it through `tangentSpaceEquivDerivation`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace CompleteLocalAlgCat

/-- `CotangentSpace S.carrier` is a `k`-vector space via the residue identification
`S.residueFieldIso`. -/
instance instModule_cotangentSpace (S : CompleteLocalAlgCat Λ k) :
    Module k (CotangentSpace S.carrier) :=
  Module.compHom (CotangentSpace S.carrier) S.residueFieldIso.symm.toRingHom

/-- The `k`-span of the image of `ker (algebraMap Λ k)` in
`CotangentSpace S.carrier`. -/
def relativeCotangentSpan (S : CompleteLocalAlgCat Λ k) :
    Submodule k (CotangentSpace S.carrier) :=
  Submodule.span k
    ((maximalIdeal S.carrier).toCotangent ''
      { x : maximalIdeal S.carrier |
        (x : S.carrier) ∈ (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S.carrier) })

/-- `relativeCotangentSpan S` is the `k`-span of the image of
`ker (algebraMap Λ k)` in `CotangentSpace S.carrier`. -/
theorem relativeCotangentSpan_spec (S : CompleteLocalAlgCat Λ k) :
    relativeCotangentSpan S =
      Submodule.span k
        ((maximalIdeal S.carrier).toCotangent ''
          { x : maximalIdeal S.carrier |
            (x : S.carrier) ∈ (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S.carrier) }) :=
  rfl

/-- Membership in `relativeCotangentSpan S` is membership in the `k`-span of the
image of `ker (algebraMap Λ k)`. -/
theorem mem_relativeCotangentSpan {S : CompleteLocalAlgCat Λ k}
    {x : CotangentSpace S.carrier} :
    x ∈ relativeCotangentSpan S ↔
      x ∈ Submodule.span k
        ((maximalIdeal S.carrier).toCotangent ''
          { y : maximalIdeal S.carrier |
            (y : S.carrier) ∈ (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S.carrier) }) :=
  Iff.rfl

/-- The relative cotangent space `T_{S/Λ}` of `S` over `Λ`, as a `k`-vector space
`m_S / (m_Λ S + m_S²)`. -/
abbrev relativeCotangentSpace (S : CompleteLocalAlgCat Λ k) : Type u :=
  CotangentSpace S.carrier ⧸ relativeCotangentSpan S

/-- `relativeCotangentSpace S` is a `k`-vector space. -/
instance instModule_relativeCotangentSpace (S : CompleteLocalAlgCat Λ k) :
    Module k (relativeCotangentSpace S) :=
  inferInstance

namespace RelativeCotangentSpace

/-- The class of an element of `maximalIdeal S.carrier` in
`relativeCotangentSpace S`. -/
def mk (S : CompleteLocalAlgCat Λ k) (x : maximalIdeal S.carrier) :
    relativeCotangentSpace S :=
  Submodule.Quotient.mk ((maximalIdeal S.carrier).toCotangent x)

/-- The class of `x` vanishes if and only if the underlying element lies in
`relativeDenom S`. -/
theorem mk_eq_zero_iff (S : CompleteLocalAlgCat Λ k) (x : maximalIdeal S.carrier) :
    mk S x = 0 ↔ (x : S.carrier) ∈ relativeDenom S := sorry

end RelativeCotangentSpace

/-- Restriction of a `Λ`-derivation `S.carrier → k` to the maximal ideal. -/
def derivationOnMaximalIdeal (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    maximalIdeal S.carrier →ₗ[Λ] k :=
  D.toLinearMap.comp ((maximalIdeal S.carrier).subtype.restrictScalars Λ)

/-- `derivationOnMaximalIdeal` evaluates as the underlying derivation. -/
theorem derivationOnMaximalIdeal_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) (x : maximalIdeal S.carrier) :
    derivationOnMaximalIdeal S D x = D (x : S.carrier) :=
  rfl

/-- A `Λ`-derivation `S.carrier → k` vanishes on products in the maximal ideal,
so it lifts through `toCotangent`. -/
theorem derivationOnMaximalIdeal_mul (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) (x y : maximalIdeal S.carrier) :
    derivationOnMaximalIdeal S D (x * y) = 0 := sorry

/-- The `k`-linear form on `CotangentSpace S.carrier` induced by a `Λ`-derivation. -/
def derivationToCotangentDual (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    CotangentSpace S.carrier →ₗ[k] k where
  toFun := Ideal.Cotangent.lift (derivationOnMaximalIdeal S D)
    (derivationOnMaximalIdeal_mul S D)
  map_add' := sorry
  map_smul' := sorry

/-- `derivationToCotangentDual` evaluates as the derivation on representatives. -/
theorem derivationToCotangentDual_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) (x : maximalIdeal S.carrier) :
    derivationToCotangentDual S D ((maximalIdeal S.carrier).toCotangent x) =
      D (x : S.carrier) := sorry

/-- The relative span lies in the kernel of `derivationToCotangentDual`. -/
theorem relativeCotangentSpan_le_ker_derivationToCotangentDual
    (S : CompleteLocalAlgCat Λ k) (D : Derivation Λ S.carrier k) :
    relativeCotangentSpan S ≤ LinearMap.ker (derivationToCotangentDual S D) := sorry

/-- The canonical pairing of `Λ`-derivations `S.carrier → k` with
`relativeCotangentSpace S`. -/
def derivationToRelativeCotangentDual (S : CompleteLocalAlgCat Λ k) :
    Derivation Λ S.carrier k →ₗ[k] (relativeCotangentSpace S →ₗ[k] k) where
  toFun D :=
    (relativeCotangentSpan S).liftQ (derivationToCotangentDual S D)
      (relativeCotangentSpan_le_ker_derivationToCotangentDual S D)
  map_add' := sorry
  map_smul' := sorry

/-- `derivationToRelativeCotangentDual` evaluates as the derivation on
`RelativeCotangentSpace.mk`. -/
theorem derivationToRelativeCotangentDual_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) (x : maximalIdeal S.carrier) :
    derivationToRelativeCotangentDual S D (RelativeCotangentSpace.mk S x) =
      D (x : S.carrier) := sorry

/-- When `k / residueImage Λ k` is separable, the pairing of derivations with
`relativeCotangentSpace S` is bijective. -/
theorem bijective_derivationToRelativeCotangentDual (S : CompleteLocalAlgCat Λ k)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    Function.Bijective (derivationToRelativeCotangentDual S) := sorry

/-- In the classical case, `k` is separable over `residueImage Λ k`. -/
instance instIsSeparable_residueImage_of_isClassical
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    Algebra.IsSeparable (Algebra.residueImage Λ k) k := sorry

end CompleteLocalAlgCat

namespace CategoryTheory.Functor.IsPredeformationFunctor

open CompleteLocalAlgCat

/-- The canonical pairing of `tangentSpace (restrictedCoyoneda S)` with
`relativeCotangentSpace S`, obtained by composing `tangentSpaceEquivDerivation`
with `derivationToRelativeCotangentDual`. -/
def tangentSpaceToRelativeCotangentDual (S : CompleteLocalAlgCat Λ k) :
    tangentSpace (restrictedCoyoneda S) →ₗ[k] (relativeCotangentSpace S →ₗ[k] k) where
  toFun x := derivationToRelativeCotangentDual S (tangentSpaceEquivDerivation S x)
  map_add' := sorry
  map_smul' := sorry

/-- `tangentSpaceToRelativeCotangentDual` evaluates as the associated derivation
on `RelativeCotangentSpace.mk`. -/
theorem tangentSpaceToRelativeCotangentDual_apply (S : CompleteLocalAlgCat Λ k)
    (x : tangentSpace (restrictedCoyoneda S)) (y : maximalIdeal S.carrier) :
    tangentSpaceToRelativeCotangentDual S x (RelativeCotangentSpace.mk S y) =
      tangentSpaceEquivDerivation S x (y : S.carrier) := sorry

end CategoryTheory.Functor.IsPredeformationFunctor

end

