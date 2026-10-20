module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ShortComplex

/-!
# Exact sequences for `Tor`

@stack 00M0
@stack 0H7P

This leaf owns the low-degree `Tor`/tensor sequence and the adjacent
five-term segments of the long exact `Tor` sequence. A connecting morphism
is explicit data: the existence theorems provide it, while sequence consumers
can retain the particular boundary morphism relevant to their argument.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]

/-- The five-term `Tor_{n + 1}`/`Tor_n` segment associated to a chosen
connecting morphism for a short complex of `R`-modules. -/
@[stacks 00M0 "Tor exact sequence"]
def succFiveTerm (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (n : ℕ)
    (δ : (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).obj S.X₃) ⟶
      (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj S.X₁)) :
    ComposableArrows (ModuleCat R) 5 :=
  ComposableArrows.mk₅
    (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).map S.f)
    (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).map S.g)
    δ
    (((CategoryTheory.Tor (ModuleCat R) n).obj M).map S.f)
    (((CategoryTheory.Tor (ModuleCat R) n).obj M).map S.g)

/-- Every short exact sequence of `R`-modules supplies the corresponding
five-term segment of the long exact `Tor` sequence. -/
@[stacks 00M0 "Tor exact sequence"]
theorem exists_succFiveTerm_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (n : ℕ) :
    ∃ δ : (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).obj S.X₃) ⟶
        (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj S.X₁),
      (succFiveTerm M n δ).Exact := sorry

/-- The same-degree exactness window in the long exact `Tor` sequence. -/
@[stacks 00M0 "Tor exact sequence"]
theorem exact_of_shortExact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((CategoryTheory.Tor (ModuleCat R) n).obj M).map S.f).hom
      (((CategoryTheory.Tor (ModuleCat R) n).obj M).map S.g).hom := sorry

/-- The two exact windows adjacent to a connecting morphism in the positive-degree
`Tor` sequence. -/
@[stacks 00M0 "Tor exact sequence"]
theorem exists_succBoundary_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (n : ℕ) :
    ∃ δ : (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).obj S.X₃) ⟶
        (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj S.X₁),
      Function.Exact (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).map S.g).hom δ.hom ∧
        Function.Exact δ.hom (((CategoryTheory.Tor (ModuleCat R) n).obj M).map S.f).hom := sorry

/-- Stacks 0H7P: a morphism of modules induces an injective degree-`n` module-first `Tor` map
when the adjacent `Tor` groups of its kernel and cokernel vanish. -/
@[stacks 0H7P "Tor injectivity from kernel and cokernel vanishing"]
theorem map_injective_of_isZero_ker_cokernel
    (M : ModuleCat R) {K L : Type u}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    (u : K →ₗ[R] L) (n : ℕ)
    (hker :
      IsZero (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj
        (ModuleCat.of R (LinearMap.ker u))))
    (hcoker :
      IsZero (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).obj
        (ModuleCat.of R (L ⧸ LinearMap.range u)))) :
    Function.Injective
      (((CategoryTheory.Tor (ModuleCat R) n).obj M).map (ModuleCat.ofHom u)).hom := sorry

/-- The low-degree `Tor₁`/tensor sequence for an explicit connecting morphism. -/
@[stacks 00M0 "Tor tensor exact sequence"]
def oneTensorSequence (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (δ : (((CategoryTheory.Tor (ModuleCat R) 1).obj M).obj S.X₃) ⟶ (M ⊗ S.X₁)) :
    ComposableArrows (ModuleCat R) 6 :=
  (ComposableArrows.mk₅
      (((CategoryTheory.Tor (ModuleCat R) 1).obj M).map S.g)
      δ
      ((tensorLeft M).map S.f)
      ((tensorLeft M).map S.g)
      (0 : (M ⊗ S.X₃) ⟶ ⊤_ (ModuleCat R))).precomp
    (((CategoryTheory.Tor (ModuleCat R) 1).obj M).map S.f)

/-- A five-term low-degree `Tor`/tensor row extends to the full six-term row because
tensoring is right exact. -/
@[stacks 00M0 "Tor tensor exact sequence"]
theorem oneTensorSequence_exact_of_fiveTerm (M : ModuleCat R)
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    {δ : (((CategoryTheory.Tor (ModuleCat R) 1).obj M).obj S.X₃) ⟶ (M ⊗ S.X₁)}
    (hδ :
      (ComposableArrows.mk₅
        (((CategoryTheory.Tor (ModuleCat R) 1).obj M).map S.f)
        (((CategoryTheory.Tor (ModuleCat R) 1).obj M).map S.g)
        δ
        ((tensorLeft M).map S.f)
        ((tensorLeft M).map S.g)).Exact) :
    (oneTensorSequence M δ).Exact := sorry

/-- Every short exact sequence of `R`-modules has an exact low-degree
`Tor₁`/tensor six-term sequence. -/
@[stacks 00M0 "Tor tensor exact sequence"]
theorem exists_oneTensorSequence_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) :
    ∃ δ : (((CategoryTheory.Tor (ModuleCat R) 1).obj M).obj S.X₃) ⟶ (M ⊗ S.X₁),
      (oneTensorSequence M δ).Exact := sorry

/-- The two low-degree exactness windows sharing the connecting morphism
`Tor₁(M, S.X₃) ⟶ M ⊗ S.X₁`. -/
@[stacks 00M0 "Tor tensor exact sequence"]
theorem exists_oneTensorBoundary_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) :
    ∃ δ : (((CategoryTheory.Tor (ModuleCat R) 1).obj M).obj S.X₃) ⟶ (M ⊗ S.X₁),
      Function.Exact (((CategoryTheory.Tor (ModuleCat R) 1).obj M).map S.g).hom δ.hom ∧
        Function.Exact δ.hom ((tensorLeft M).map S.f).hom := sorry

/-- The low-degree `Tor₁`/tensor boundary in raw linear-map form for a short exact
sequence of `R`-modules. This is the concrete companion to
`exists_oneTensorBoundary_exact`; it avoids rebuilding a `ShortComplex` merely to use
`LinearMap.lTensor`. -/
@[stacks 00M0 "Tor tensor exact sequence"]
theorem exists_lTensorBoundary_exact
    (M : Type u) [AddCommGroup M] [Module R M]
    {X₁ X₂ X₃ : Type u}
    [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup X₃] [Module R X₃]
    (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hExact : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    ∃ δ : (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R X₃)) ⟶ ModuleCat.of R (M ⊗[R] X₁),
      Function.Exact
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map (ModuleCat.ofHom g)).hom
        δ.hom ∧
        Function.Exact δ.hom (f.lTensor M) := sorry

end CategoryTheory.ModuleCat.Tor

namespace CategoryTheory.ModuleCat.Tor'

variable {R : Type u} [CommRing R]

/-- The five-term `Tor'_{n + 1}`/`Tor'_n` segment associated to a chosen
connecting morphism for a short complex of `R`-modules. -/
@[stacks 00M0 "Tor exact sequence"]
def succFiveTerm (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (n : ℕ)
    (δ : (((CategoryTheory.Tor' (ModuleCat R) (n + 1)).obj M).obj S.X₃) ⟶
      (((CategoryTheory.Tor' (ModuleCat R) n).obj M).obj S.X₁)) :
    ComposableArrows (ModuleCat R) 5 :=
  ComposableArrows.mk₅
    (((CategoryTheory.Tor' (ModuleCat R) (n + 1)).obj M).map S.f)
    (((CategoryTheory.Tor' (ModuleCat R) (n + 1)).obj M).map S.g)
    δ
    (((CategoryTheory.Tor' (ModuleCat R) n).obj M).map S.f)
    (((CategoryTheory.Tor' (ModuleCat R) n).obj M).map S.g)

/-- Every short exact sequence of `R`-modules supplies the corresponding
five-term segment of the long exact `Tor'` sequence. -/
@[stacks 00M0 "Tor exact sequence"]
theorem exists_succFiveTerm_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (n : ℕ) :
    ∃ δ : (((CategoryTheory.Tor' (ModuleCat R) (n + 1)).obj M).obj S.X₃) ⟶
        (((CategoryTheory.Tor' (ModuleCat R) n).obj M).obj S.X₁),
      (succFiveTerm M n δ).Exact := sorry

/-- The same-degree exactness window in the fixed-left derived `Tor'` sequence. -/
@[stacks 00M0 "Tor exact sequence"]
theorem exact_of_shortExact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((CategoryTheory.Tor' (ModuleCat R) n).obj M).map S.f).hom
      (((CategoryTheory.Tor' (ModuleCat R) n).obj M).map S.g).hom := sorry

/-- The two exact windows adjacent to a connecting morphism in the positive-degree
`Tor'` sequence. -/
@[stacks 00M0 "Tor exact sequence"]
theorem exists_succBoundary_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (n : ℕ) :
    ∃ δ : (((CategoryTheory.Tor' (ModuleCat R) (n + 1)).obj M).obj S.X₃) ⟶
        (((CategoryTheory.Tor' (ModuleCat R) n).obj M).obj S.X₁),
      Function.Exact (((CategoryTheory.Tor' (ModuleCat R) (n + 1)).obj M).map S.g).hom δ.hom ∧
        Function.Exact δ.hom (((CategoryTheory.Tor' (ModuleCat R) n).obj M).map S.f).hom := sorry

end CategoryTheory.ModuleCat.Tor'
