/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Order.Bounds.Basic
public import stacks_project.Chap66.Definition_66_29_1_QCoh

/-!
# Largest quasicoherent subobjects on algebraic spaces

This file owns the universal largest quasicoherent subobject contained in a prescribed
subobject of a quasicoherent module on an algebraic space.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A quasicoherent subobject through which every map from a quasicoherent module factors
uniquely is greatest among the quasicoherent subobjects of the prescribed subobject. -/
theorem isGreatest_of_quasiCoherent_hom_bijective
    (F : X.Modules) [F.IsQuasicoherent] (G G' : Subobject F) (hG' : G' ≤ G)
    (qG' : (G' : X.Modules).IsQuasicoherent)
    (h_bijective : ∀ H : X.QCoh,
      Function.Bijective
        (fun phi : H.obj ⟶ (G' : X.Modules) => phi ≫ Subobject.ofLE G' G hG')) :
    IsGreatest (setOf fun G'' : Subobject F =>
      (G'' : X.Modules).IsQuasicoherent ∧ G'' ≤ G) G' := sorry

/-- Every subobject of a quasicoherent module on an algebraic space contains a unique
largest quasicoherent subobject, characterized by maps from quasicoherent modules. -/
theorem existsUnique_largestQuasiCoherentSubobject
    (F : X.Modules) [F.IsQuasicoherent] (G : Subobject F) :
    ∃! G' : Subobject F,
      ∃ hG' : G' ≤ G,
        (G' : X.Modules).IsQuasicoherent ∧
        ∀ H : X.QCoh,
          Function.Bijective
            (fun phi : H.obj ⟶ (G' : X.Modules) => phi ≫ Subobject.ofLE G' G hG') := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
