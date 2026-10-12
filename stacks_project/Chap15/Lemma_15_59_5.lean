/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.Triangulated
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksCheckRecall

/-!
Lemma 15.59.5 (06Y2): K-flat objects satisfy two-out-of-three for distinguished triangles in
`K(R)`.  The reusable owner is `CategoryTheory.HomotopyCategory.IsKFlat` together with its
distinguished-triangle API.  This file records the current `ModuleCat` specialization for a
commutative ring; the generic owner itself applies to every monoidal preadditive category with
the required biproducts.

@stack 06Y2
-/

open CategoryTheory CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory

noncomputable section

universe u

namespace CategoryTheory.HomotopyCategory

variable (R : Type u) [CommRing R]

/- Lemma 15.59.5 (06Y2), in the three source-facing two-out-of-three forms. -/
@[stacks 06Y2 "third vertex of a distinguished triangle"]
#check
  (IsKFlat.obj₃_of_distinguished :
    (T : Triangle (HomotopyCategory (ModuleCat R) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (ModuleCat R) (up ℤ)) →
        T.obj₁.IsKFlat → T.obj₂.IsKFlat → T.obj₃.IsKFlat)
@[stacks 06Y2 "second vertex of a distinguished triangle"]
#check
  (IsKFlat.obj₂_of_distinguished :
    (T : Triangle (HomotopyCategory (ModuleCat R) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (ModuleCat R) (up ℤ)) →
        T.obj₁.IsKFlat → T.obj₃.IsKFlat → T.obj₂.IsKFlat)
@[stacks 06Y2 "first vertex of a distinguished triangle"]
#check
  (IsKFlat.obj₁_of_distinguished :
    (T : Triangle (HomotopyCategory (ModuleCat R) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (ModuleCat R) (up ℤ)) →
        T.obj₂.IsKFlat → T.obj₃.IsKFlat → T.obj₁.IsKFlat)

end CategoryTheory.HomotopyCategory
