/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Augmented Low-Degree Exact Windows

The ordinary low-degree window begins at `F⁰(X₁)`. This leaf adjoins the
canonical zero morphism on the left, producing the standard seven-object
exact sequence beginning with the zero object.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- The low-degree exact window augmented on the left by the zero object:
`0 ⟶ F⁰(X₁) ⟶ F⁰(X₂) ⟶ F⁰(X₃) ⟶ F¹(X₁) ⟶ F¹(X₂) ⟶ F¹(X₃)`. -/
@[stacks 010Q "augmented low-degree cohomological exact window"]
def augmentedWindow (F : CohomologicalDeltaFunctor A B)
    [HasZeroObject B]
    {S : ShortComplex A} (hS : S.ShortExact) : ComposableArrows B 6 :=
  (F.lowDegreeWindow hS).zeroPrecomp 1

variable [HasZeroObject B]

/-- The augmented low-degree cohomological window is exact. -/
@[stacks 010Q "exactness of the augmented low-degree cohomological window"]
theorem augmentedWindow_exact (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).Exact := sorry

namespace augmentedWindow

/-- Removing the initial zero morphism recovers the ordinary low-degree
window. -/
@[simp]
theorem δ₀ (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).δ₀ = F.lowDegreeWindow hS := sorry

/-- The first arrow of the augmented window is the canonical zero morphism. -/
@[simp]
theorem map_zero_one (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).map' 0 1 =
      (0 : (0 : B) ⟶ (F.F 0).obj.obj S.X₁) := sorry

/-- The next arrow is the degree-zero image of the first short-complex map. -/
@[simp]
theorem map_f_zero (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).map' 1 2 = (F.F 0).obj.map S.f := sorry

/-- The third arrow is the degree-zero image of the second short-complex map. -/
@[simp]
theorem map_g_zero (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).map' 2 3 = (F.F 0).obj.map S.g := sorry

/-- The middle arrow is the degree-zero connecting morphism. -/
@[simp]
theorem connecting_zero (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).map' 3 4 = F.δ hS 0 := sorry

/-- The fifth arrow is the degree-one image of the first short-complex map. -/
@[simp]
theorem map_f_one (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).map' 4 5 = (F.F 1).obj.map S.f := sorry

/-- The last arrow is the degree-one image of the second short-complex map. -/
@[simp]
theorem map_g_one (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.augmentedWindow hS).map' 5 6 = (F.F 1).obj.map S.g := sorry

end augmentedWindow

end CategoryTheory.CohomologicalDeltaFunctor
