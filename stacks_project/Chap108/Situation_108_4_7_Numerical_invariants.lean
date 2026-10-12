/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Situation_108_4_7_Numerical_invariants_Euler
public import stacks_project.Chap108.Situation_108_4_7_Numerical_invariants_Substack

/-!
# Situation 108.4.7 (Numerical invariants)

For `f : X ⟶ B` separated of finite presentation, a family of perfect objects
`E i` of `D(𝒪_X)`, and a function `P : I → ℤ`, each object of `CohStack f`
determines perfect objects `K_i` whose formation commutes with base change and
locally constant Euler characteristics `χ_i`. The substack `Coh^P_{X/B}` is the
full subcategory of objects with `χ_i(t) = P i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Situation 108.4.7 (Numerical invariants) (1): for `f : X ⟶ B` separated of
finite presentation, a perfect object `E i` of `D(𝒪_X)`, and an object
`(T ⟶ B, F)` of `CohStack f`, the object
`K_i = Rf_{T,*}(E_{i,T} ⊗ᴸ F[0])` of `D(𝒪_T)` is perfect. -/
@[stacks 0DNC]
theorem numericalPushforward_isPerfect (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) (x : Obj f) (i : I) :
    ModuleDerived.IsPerfect (x.numericalPushforward (E i)) :=
  sorry

/-- Situation 108.4.7 (Numerical invariants) (2): formation of `K_i` commutes
with base change along a morphism of `CohStack f`. -/
@[stacks 0DNC]
theorem numericalPushforward_baseChange (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) {x y : Obj f} (α : Hom x y)
    (i : I) :
    Nonempty
      ((ModuleDerived.pullback (ofOverMap α.base.left)).obj
          (y.numericalPushforward (E i)) ≅
        x.numericalPushforward (E i)) :=
  sorry

/-- Situation 108.4.7 (Numerical invariants) (3): the function
`χ_i : |T| ⟶ ℤ` given by `χ_i(t) = χ(K_i ⊗ᴸ κ(t))` is locally constant. -/
@[stacks 0DNC]
theorem eulerChar_isLocallyConstant (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) (x : Obj f) (i : I) :
    IsLocallyConstant (x.eulerChar (E i)) :=
  sorry

/-- Situation 108.4.7 (Numerical invariants) (4): an object `(T ⟶ B, F)` of
`CohStack f` lies in the substack `Coh^P_{X/B}` if and only if `χ_i(t) = P i`
for all `i ∈ I` and all points `t` of `T`. -/
@[stacks 0DNC]
theorem mem_Numerical (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ) (x : Obj f) :
    numerical f E P x ↔ ∀ i t, x.eulerChar (E i) t = P i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
