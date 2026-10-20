/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.26.6 (079S): in a distinguished triangle in
`K(Mod(𝒪_X))`, K-flatness is a two-out-of-three property.  The reusable owner is the generic
homotopy-category K-flat API; this file is only its ringed-space specialization. -/

variable {X : RingedSpace.{u}}

/- The owner theorem with the third vertex as conclusion. -/
@[stacks 079S "third vertex"]
#check
  (CategoryTheory.HomotopyCategory.IsKFlat.obj₃_of_distinguished :
    (T : Triangle (HomotopyCategory (Modules X) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (Modules X) (up ℤ)) →
      T.obj₁.IsKFlat → T.obj₂.IsKFlat → T.obj₃.IsKFlat)

/- The owner theorem with the middle vertex as conclusion. -/
@[stacks 079S "middle vertex"]
#check
  (CategoryTheory.HomotopyCategory.IsKFlat.obj₂_of_distinguished :
    (T : Triangle (HomotopyCategory (Modules X) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (Modules X) (up ℤ)) →
      T.obj₁.IsKFlat → T.obj₃.IsKFlat → T.obj₂.IsKFlat)

/- The owner theorem with the first vertex as conclusion. -/
@[stacks 079S "first vertex"]
#check
  (CategoryTheory.HomotopyCategory.IsKFlat.obj₁_of_distinguished :
    (T : Triangle (HomotopyCategory (Modules X) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (Modules X) (up ℤ)) →
      T.obj₂.IsKFlat → T.obj₃.IsKFlat → T.obj₁.IsKFlat)

#print axioms CategoryTheory.HomotopyCategory.IsKFlat.obj₃_of_distinguished
#print axioms CategoryTheory.HomotopyCategory.IsKFlat.obj₂_of_distinguished
#print axioms CategoryTheory.HomotopyCategory.IsKFlat.obj₁_of_distinguished

end AlgebraicGeometry.RingedSpace
