module

public import stacks_project.Chap91.Lemma_91_15_1_CanonicalClass
public import stacks_project.Chap91.Lemma_91_15_1_Kernel
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Canonical class of a complex along a square-zero surjection

For a square-zero surjection `R' → R` with kernel `I`, every `K` in `D⁻(R)` has a canonical
morphism `ω(K) : K ⟶ K ⊗[R]^L I[2]` in `D(R)` that vanishes if and only if `K` lifts to `D(R')`,
is natural in morphisms of `D⁻(R)`, and is compatible with base change along `R' → S'`.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace ModuleCat.SquareZeroExtension

variable {R' R : Type u} [CommRing R'] [CommRing R]

/- Lemma 91.15.1 (1): Let `R' → R` be a surjection of rings whose kernel is an ideal `I` of square
zero. For every `K` in `D⁻(R)` there is a canonical map
`ω(K) : K ⟶ K ⊗[R]^L I[2]` in `D(R)`. -/
@[stacks 0DYR] #check canonicalClass

/-- Lemma 91.15.1 (2): `ω(K) = 0` if and only if there exists `K'` in `D(R')` with
`K' ⊗[R']^L R` isomorphic to `K`. -/
@[stacks 0DYR]
theorem canonicalClass_eq_zero_iff (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    canonicalClass f K hK = 0 ↔
      ∃ K' : DerivedCategory (ModuleCat.{u} R'),
        IsIsomorphic ((ModuleCat.derivedExtensionOfScalars f).obj K') K := sorry

/-- Lemma 91.15.1 (3): given `α : K ⟶ L` in `D⁻(R)`, the square relating `ω(K)` and `ω(L)`
commutes. -/
@[stacks 0DYR]
theorem canonicalClass_natural (f : R' →+* R) [f.IsSquareZeroExtension]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (hK : K.IsBoundedAbove) (hL : L.IsBoundedAbove) (α : K ⟶ L) :
    canonicalClass f K hK ≫ tensorKernelShiftMap f α =
      α ≫ canonicalClass f L hL := sorry

variable {S' : Type u} [CommRing S']

/-- Lemma 91.15.1 (4): formation of `ω(K)` is compatible with a ring map `R' → S'` in the
sense that if `S = S' ⊗[R'] R` and `J = ker(S' → S)`, then
`(ω(K) ⊗ id_S)` equals `ω(K ⊗[R]^L S)` after the comparison
`(K ⊗[R]^L I[2]) ⊗[R]^L S ⟶ (K ⊗[R]^L S) ⊗[S]^L J[2]` induced by `I ⊗[R] S ⟶ J`. -/
@[stacks 0DYR]
theorem canonicalClass_baseChange (f : R' →+* R) [f.IsSquareZeroExtension]
    (g : R' →+* S') (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) :
    (ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g)).map
          (canonicalClass f K hK) ≫
        kernelBaseChangeDerived f g K =
      canonicalClass (tensorCodomainRingHom f g)
        ((ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g)).obj K)
        (derivedExtensionOfScalars_isBoundedAbove
          (tensorCodomainIncludeRight f g) K hK) := sorry

end ModuleCat.SquareZeroExtension
