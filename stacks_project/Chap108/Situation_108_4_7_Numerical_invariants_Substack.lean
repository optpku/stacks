/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap99.Lemma_99_5_2
public import stacks_project.Chap108.Situation_108_4_7_Numerical_invariants_Euler

/-!
# Numerical substack of coherent sheaves

The full subcategory of `CohStack f` on objects whose Euler characteristics
`χ_i` agree with a prescribed function `P : I → ℤ`, packaged as a category
fibred in groupoids over `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.BasedFunctor CategoryTheory.FiberedCategoryOver.Groupoids
open CategoryTheory.ObjectProperty
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- An object of `CohStack f` has numerical invariants `P` with respect to a
family `E` if `χ_i(t) = P i` at every index and every point of the test
scheme. -/
def Obj.HasNumerical {f : X ⟶ B} [FinitePresentation f] {I : Type u}
    (x : Obj f) (E : I → ModuleDerived X) (P : I → ℤ) : Prop :=
  ∀ i t, x.eulerChar (E i) t = P i

/-- `HasNumerical` unpacks as the pointwise Euler-characteristic condition. -/
theorem Obj.HasNumerical_iff {f : X ⟶ B} [FinitePresentation f] {I : Type u}
    (x : Obj f) (E : I → ModuleDerived X) (P : I → ℤ) :
    x.HasNumerical E P ↔ ∀ i t, x.eulerChar (E i) t = P i :=
  sorry

/-- The object property of `CohStack f` cut out by numerical invariants `P`. -/
def numerical (f : X ⟶ B) [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) : ObjectProperty (Obj f) :=
  fun x ↦ x.HasNumerical E P

/-- Membership in `numerical f E P` is `HasNumerical`. -/
theorem mem_numerical {f : X ⟶ B} [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (x : Obj f) :
    numerical f E P x ↔ x.HasNumerical E P :=
  sorry

/-- The full subcategory of `CohStack f` on objects whose numerical invariants
agree with `P`. -/
abbrev Numerical (f : X ⟶ B) [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) :=
  (numerical f E P).FullSubcategory

/-- Package an object of `CohStack f` satisfying `HasNumerical` as an object of
`Numerical f E P`. -/
def Numerical.of {f : X ⟶ B} [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (x : Obj f) (hx : x.HasNumerical E P) :
    Numerical f E P :=
  ⟨x, hx⟩

/-- The underlying `CohStack` object of `Numerical.of` is the supplied object. -/
theorem Numerical.of_obj {f : X ⟶ B} [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (x : Obj f) (hx : x.HasNumerical E P) :
    (Numerical.of E P x hx).obj = x :=
  sorry

/-- An object of `CohStack f` lies in `Numerical f E P` if and only if
`χ_i(t) = P i` for all indices `i` and all points `t` of the test scheme. -/
theorem Numerical.mem_iff {f : X ⟶ B} [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (x : Obj f) :
    numerical f E P x ↔ ∀ i t, x.eulerChar (E i) t = P i :=
  sorry

/-- Restriction along a morphism of `CohStack` objects preserves the numerical
invariant condition. -/
theorem Hom.hasNumerical {f : X ⟶ B} [FinitePresentation f] {I : Type u}
    {x y : Obj f} (α : Hom x y) (E : I → ModuleDerived X)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) (P : I → ℤ)
    (hy : y.HasNumerical E P) : x.HasNumerical E P :=
  sorry

/-- The restricted projection of the numerical full subcategory is fibred in
groupoids, for a family of perfect derived modules. -/
theorem isFiberedInGroupoids_numerical (f : X ⟶ B) [FinitePresentation f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Functor.IsFibered.InGroupoids ((numerical f E P).ι ⋙ p f) :=
  sorry

/-- The numerical substack as a category fibred in groupoids over `Over S`. -/
def toGroupoidsNumerical (f : X ⟶ B) [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  ⟨BasedCategory.ofFunctor ((numerical f E P).ι ⋙ p f),
    isFiberedInGroupoids_numerical f E P hE⟩

/-- The projection of `toGroupoidsNumerical` is the restricted `p f`. -/
theorem toGroupoidsNumerical_p (f : X ⟶ B) [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (toGroupoidsNumerical f E P hE).p = (numerical f E P).ι ⋙ p f :=
  sorry

/-- The total category of `toGroupoidsNumerical` is `Numerical f E P`. -/
theorem toGroupoidsNumerical_total (f : X ⟶ B) [FinitePresentation f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (toGroupoidsNumerical f E P hE).total = Numerical f E P :=
  sorry

/-- The inclusion `Coh^P_{X/B} ⟶ Coh_{X/B}` of categories fibred in groupoids
over `Over S`. -/
def Numerical.ι (f : X ⟶ B) [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    toGroupoidsNumerical f E P hE ⟶ toGroupoids f :=
  ofBasedFunctor (BasedFunctor.ofFunctor (numerical f E P).ι rfl)

/-- Forgetting `Numerical.ι` to based functors recovers `BasedFunctor.ofFunctor`
of the full-subcategory inclusion. -/
theorem Numerical.ι_toBasedFunctor (f : X ⟶ B) [FinitePresentation f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (Numerical.ι f E P hE) =
      BasedFunctor.ofFunctor (numerical f E P).ι rfl :=
  sorry

/-- The underlying functor of `Numerical.ι` is the full-subcategory inclusion. -/
theorem Numerical.ι_toFunctor (f : X ⟶ B) [FinitePresentation f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    FiberedCategoryOver.Groupoids.toFunctor (Numerical.ι f E P hE) =
      (numerical f E P).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
