module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Iso
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Triangulated Closure for Computing Pointwise Derived Values

This leaf makes the object properties of points computing pointwise derived values available to
the standard triangulated-subcategory API.  It is deliberately stated for an arbitrary
shift-compatible localization class, rather than for a particular derived-category presentation.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits MorphismProperty ObjectProperty Pretriangulated

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  {F : D ⥤ D'} {S : MorphismProperty D}
  [S.ContainsIdentities]

/-- Stacks 05SZ: points computing a pointwise right-derived value are closed under the third
vertex of a distinguished triangle. -/
@[stacks 05SZ]
instance RightDerived.ComputesAt.triangulatedClosed₃
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D'] :
    IsTriangulatedClosed₃ (RightDerived.ComputesAt.objects F S) := sorry

/-- Stacks 05SZ: points computing a pointwise left-derived value are closed under the third
vertex of a distinguished triangle. -/
@[stacks 05SZ]
instance LeftDerived.ComputesAt.triangulatedClosed₃
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D'] :
    IsTriangulatedClosed₃ (LeftDerived.ComputesAt.objects F S) := sorry

/-- Points computing a pointwise right-derived value are closed under the second vertex of a
distinguished triangle. -/
@[stacks 05SZ "right-derived second-vertex closure"]
instance RightDerived.ComputesAt.triangulatedClosed₂
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D'] :
    IsTriangulatedClosed₂ (RightDerived.ComputesAt.objects F S) := sorry

/-- Points computing a pointwise left-derived value are closed under the second vertex of a
distinguished triangle. -/
@[stacks 05SZ "left-derived second-vertex closure"]
instance LeftDerived.ComputesAt.triangulatedClosed₂
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D'] :
    IsTriangulatedClosed₂ (LeftDerived.ComputesAt.objects F S) := sorry

/-- Points computing a pointwise right-derived value are closed under the first vertex of a
distinguished triangle. -/
@[stacks 05SZ "right-derived first-vertex closure"]
instance RightDerived.ComputesAt.triangulatedClosed₁
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D'] :
    IsTriangulatedClosed₁ (RightDerived.ComputesAt.objects F S) := sorry

/-- Points computing a pointwise left-derived value are closed under the first vertex of a
distinguished triangle. -/
@[stacks 05SZ "left-derived first-vertex closure"]
instance LeftDerived.ComputesAt.triangulatedClosed₁
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D'] :
    IsTriangulatedClosed₁ (LeftDerived.ComputesAt.objects F S) := sorry

/-- If the last two vertices of a distinguished triangle compute the pointwise right-derived
value, then so does the first vertex. -/
@[stacks 05SZ "right-derived two-out-of-three, first vertex"]
theorem RightDerived.ComputesAt.obj₁_of_triangle
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₂ : RightDerived.ComputesAt F S T.obj₂)
    (h₃ : RightDerived.ComputesAt F S T.obj₃) :
    RightDerived.ComputesAt F S T.obj₁ := sorry

/-- If the first and third vertices of a distinguished triangle compute the pointwise
right-derived value, then so does the second vertex. -/
@[stacks 05SZ "right-derived two-out-of-three, second vertex"]
theorem RightDerived.ComputesAt.obj₂_of_triangle
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : RightDerived.ComputesAt F S T.obj₁)
    (h₃ : RightDerived.ComputesAt F S T.obj₃) :
    RightDerived.ComputesAt F S T.obj₂ := sorry

/-- If the last two vertices of a distinguished triangle compute the pointwise left-derived
value, then so does the first vertex. -/
@[stacks 05SZ "left-derived two-out-of-three, first vertex"]
theorem LeftDerived.ComputesAt.obj₁_of_triangle
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D']
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₂ : LeftDerived.ComputesAt F S T.obj₂)
    (h₃ : LeftDerived.ComputesAt F S T.obj₃) :
    LeftDerived.ComputesAt F S T.obj₁ := sorry

/-- If the first and third vertices of a distinguished triangle compute the pointwise
left-derived value, then so does the second vertex. -/
@[stacks 05SZ "left-derived two-out-of-three, second vertex"]
theorem LeftDerived.ComputesAt.obj₂_of_triangle
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D']
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : LeftDerived.ComputesAt F S T.obj₁)
    (h₃ : LeftDerived.ComputesAt F S T.obj₃) :
    LeftDerived.ComputesAt F S T.obj₂ := sorry

/-- Stacks 05SZ: if the first two vertices of a distinguished triangle compute the pointwise
right-derived value, then so does the third vertex. -/
@[stacks 05SZ]
theorem RightDerived.ComputesAt.obj₃_of_triangle
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : RightDerived.ComputesAt F S T.obj₁)
    (h₂ : RightDerived.ComputesAt F S T.obj₂) :
    RightDerived.ComputesAt F S T.obj₃ := sorry

/-- Stacks 05SZ: if the first two vertices of a distinguished triangle compute the pointwise
left-derived value, then so does the third vertex. -/
@[stacks 05SZ]
theorem LeftDerived.ComputesAt.obj₃_of_triangle
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated D']
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : LeftDerived.ComputesAt F S T.obj₁)
    (h₂ : LeftDerived.ComputesAt F S T.obj₂) :
    LeftDerived.ComputesAt F S T.obj₃ := sorry

end CategoryTheory.Functor
