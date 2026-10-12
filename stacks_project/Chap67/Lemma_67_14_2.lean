/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_14_2_LargestSubobject
import StacksCheckRecall

/-!
# Lemma 67.14.2

The largest quasicoherent subobject contained in a prescribed subobject of a
quasicoherent module on an algebraic space.

@stack 04CK
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.14.2: Every subobject of a quasicoherent module on an algebraic space
contains a unique quasicoherent subobject characterized by unique factorization of
maps from quasicoherent modules. -/
@[stacks 04CK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.existsUnique_largestQuasiCoherentSubobject :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
      (G : Subobject F),
      ∃! G' : Subobject F,
        ∃ hG' : G' ≤ G,
          (G' : X.Modules).IsQuasicoherent ∧
          ∀ H : X.QCoh,
            Function.Bijective
              (fun phi : H.obj ⟶ (G' : X.Modules) ↦
                phi ≫ Subobject.ofLE G' G hG'))

/- The universal-property witness is greatest among quasicoherent subobjects contained in
the prescribed subobject. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isGreatest_of_quasiCoherent_hom_bijective :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
      (G G' : Subobject F) (hG' : G' ≤ G)
      (_ : (G' : X.Modules).IsQuasicoherent)
      (_ : ∀ H : X.QCoh,
        Function.Bijective
          (fun phi : H.obj ⟶ (G' : X.Modules) ↦
            phi ≫ Subobject.ofLE G' G hG')),
      IsGreatest (setOf fun G'' : Subobject F ↦
        (G'' : X.Modules).IsQuasicoherent ∧ G'' ≤ G) G')
