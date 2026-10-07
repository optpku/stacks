module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Definition_98_18_1
public import stacks_project.Chap98.Definition_98_22_1_ObstructionTheory
public import stacks_project.Chap98.Lemma_98_21_2_Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction theories imply openness of versality

On a locally Noetherian base, a category fibred in groupoids over `(Sch/S)_fppf`
with diagonal representable by algebraic spaces, (RS*), limit preservation, an
obstruction theory, countable-product preservation of `T_x`, and injective
countable-product comparison of `O_x`, satisfies openness of versality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The tangent functors `T_x` preserve countable products: the canonical
comparison `T_x(∏ᶜ M) ⟶ ∏ᶜ T_x(M n)` is an isomorphism. -/
def tangentFunctor.preservesNatPi {S : Scheme.{u}} (X : GroupoidsOver S)
    [HasStrongRimSchlessinger X] : Prop :=
  ∀ {A : CommRingCat.{u}} {σA : Spec A ⟶ S} (x : X.p.Fiber (Over.mk σA))
    (M : ℕ → ModuleCat.{u} A),
    IsIso (piComparison (tangentFunctor x) M)

/-- `preservesNatPi` means the product comparison of `tangentFunctor x` is an
isomorphism for every fibre object over `Spec(A)` and every countable family of
`A`-modules. -/
theorem tangentFunctor.preservesNatPi_iff {S : Scheme.{u}} (X : GroupoidsOver S)
    [HasStrongRimSchlessinger X] :
    tangentFunctor.preservesNatPi X ↔
      ∀ {A : CommRingCat.{u}} {σA : Spec A ⟶ S} (x : X.p.Fiber (Over.mk σA))
        (M : ℕ → ModuleCat.{u} A),
        IsIso (piComparison (tangentFunctor x) M) :=
  sorry

/-- The product comparison of `T_x` is an isomorphism. -/
theorem tangentFunctor.isIso_piComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] (h : tangentFunctor.preservesNatPi X)
    {A : CommRingCat.{u}} {σA : Spec A ⟶ S} (x : X.p.Fiber (Over.mk σA))
    (M : ℕ → ModuleCat.{u} A) :
    IsIso (piComparison (tangentFunctor x) M) :=
  sorry

/-- The obstruction-module functors `O_x` have injective countable product
comparisons: `O_x(∏ᶜ M) ⟶ ∏ᶜ O_x(M n)` is injective. -/
def ObstructionTheory.natPiComparison_injective {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (𝒪 : ObstructionTheory X) : Prop :=
  ∀ (ξ : ObjectOverSpec X) (M : ℕ → ModuleCat.{u} ξ.carrier),
    Function.Injective (piComparison (𝒪.module ξ) M).hom

/-- `natPiComparison_injective` means the underlying map of the product
comparison of `𝒪.module ξ` is injective for every object over `Spec(A)` and
every countable family of modules. -/
theorem ObstructionTheory.natPiComparison_injective_iff {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} (𝒪 : ObstructionTheory X) :
    𝒪.natPiComparison_injective ↔
      ∀ (ξ : ObjectOverSpec X) (M : ℕ → ModuleCat.{u} ξ.carrier),
        Function.Injective (piComparison (𝒪.module ξ) M).hom :=
  sorry

/-- The underlying map of the product comparison of `O_x` is injective. -/
theorem ObstructionTheory.injective_natPiComparison {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} {𝒪 : ObstructionTheory X}
    (h : 𝒪.natPiComparison_injective) (ξ : ObjectOverSpec X)
    (M : ℕ → ModuleCat.{u} ξ.carrier) :
    Function.Injective (piComparison (𝒪.module ξ) M).hom :=
  sorry

/-- Lemma 98.22.2: let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, `X` has (RS*), `X` is
limit preserving, there is an obstruction theory `𝒪`, and for an object `x`
of `X` over `Spec(A)` and `A`-modules `M n` the comparison
`T_x(∏ᶜ M) ⟶ ∏ᶜ T_x(M n)` is an isomorphism and
`O_x(∏ᶜ M) ⟶ ∏ᶜ O_x(M n)` is injective. Then `X` satisfies openness of
versality. -/
@[stacks 0CYF]
theorem OpennessOfVersality.ofObstructionTheory
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (𝒪 : ObstructionTheory X) (hT : tangentFunctor.preservesNatPi X)
    (hO : 𝒪.natPiComparison_injective) :
    OpennessOfVersality X :=
  sorry

end AlgebraicGeometry.GroupoidsOver
