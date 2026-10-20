/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Evaluation

/-!
# Structural Maps of Total Postnikov-System Stages

This file exposes the second and connecting maps of every finite Postnikov
stage as natural transformations, with their naturality and component API.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {n : ℕ}

/-- Naturality of the second maps in the stage triangles of total Postnikov systems. -/
@[reassoc, stacks 0D7Z "naturality of the second Postnikov-stage map"]
theorem toNext_naturality (i : Fin n) {P Q : Total D n} (f : P ⟶ Q) :
    f.base.app i.castSucc ≫ Q.system.toNext i =
      P.system.toNext i ≫ f.systemMap.yMap i.succ := sorry

variable (D) in
/-- The second maps of the stage triangles, as a natural transformation from the row vertex to
the next auxiliary vertex. -/
@[stacks 0D7Z "second map of a total Postnikov-stage triangle"]
def toNext (n : ℕ) (i : Fin n) : row D n i.castSucc ⟶ aux D n i.succ where
  app P := P.system.toNext i
  naturality _ _ f := toNext_naturality i f

/-- The component of `toNext` is the second map in the corresponding Postnikov-stage
triangle. -/
@[simp, stacks 0D7Z "second Postnikov-stage map component"]
theorem toNext_app (i : Fin n) (P : Total D n) :
    (toNext D n i).app P = P.system.toNext i := sorry

/-- Naturality of the connecting maps in the stage triangles of total Postnikov systems. -/
@[reassoc, stacks 0D7Z "naturality of the Postnikov-stage connecting map"]
theorem connecting_naturality (i : Fin n) {P Q : Total D n} (f : P ⟶ Q) :
    f.systemMap.yMap i.succ ≫ Q.system.connecting i =
      P.system.connecting i ≫ (shiftFunctor D (1 : ℤ)).map
        (f.systemMap.yMap i.castSucc) := sorry

variable (D) in
/-- The connecting maps of the stage triangles, as a natural transformation to the shifted
first auxiliary vertex. -/
@[stacks 0D7Z "connecting map of a total Postnikov-stage triangle"]
def connecting (n : ℕ) (i : Fin n) :
    aux D n i.succ ⟶ aux D n i.castSucc ⋙ shiftFunctor D (1 : ℤ) where
  app P := P.system.connecting i
  naturality _ _ f := connecting_naturality i f

/-- The component of `connecting` is the connecting map in the corresponding
Postnikov-stage triangle. -/
@[simp, stacks 0D7Z "Postnikov-stage connecting-map component"]
theorem connecting_app (i : Fin n) (P : Total D n) :
    (connecting D n i).app P = P.system.connecting i := sorry

end CategoryTheory.PostnikovSystem.Total
