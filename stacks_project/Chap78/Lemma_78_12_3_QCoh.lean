/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent

/-! # Quasi-coherent modules on groupoids in algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Pullback along a composite identifies canonically with successive pullbacks. -/
def pullbackCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicSpace.QCoh.pullback (f ≫ g) ≅
      AlgebraicSpace.QCoh.pullback g ⋙ AlgebraicSpace.QCoh.pullback f :=
  (AlgebraicSpace.QCoh.pullbackCompIso g f).symm

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

#check (systemCategory G : Category (System G))
#check (G.QCoh : Cat)

variable (F : AlgebraicSpace.QCoh G.U.left)
variable (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
  (AlgebraicSpace.QCoh.pullback G.s.left).obj F)
variable (cocycle : Cocycle G F action) (unit : Unit G F action)

#check (System.of F action cocycle unit : System G)
#check (QCoh.of F action cocycle unit : G.QCoh)

variable (A : G.QCoh) {M N : G.QCoh} (a : M ⟶ N)

#check (QCoh.obj A : AlgebraicSpace.QCoh G.U.left)
#check (QCoh.action A : (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj ⟶
  (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj)
#check (QCoh.hom a : M.obj ⟶ N.obj)

end AlgebraicGeometry.GroupoidAlgebraicSpace
