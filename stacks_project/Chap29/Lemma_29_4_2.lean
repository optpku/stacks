module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.LargestSubobject
import StacksCheckRecall

/-!
# Lemma 29.4.2

The largest quasicoherent subobject contained in a prescribed subobject.

@stack 01QZ
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.4.2: Every subobject of a quasicoherent module contains a unique quasicoherent
subobject characterized by unique factorization of maps from quasicoherent modules. -/
@[stacks 01QZ] #check
  (AlgebraicGeometry.Scheme.Modules.existsUnique_largestQuasiCoherentSubobject :
    ∀ {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (G : Subobject F),
      ∃! G' : Subobject F,
        ∃ hG' : G' ≤ G,
          (G' : X.Modules).IsQuasicoherent ∧
          ∀ H : X.QCoh,
            Function.Bijective
              (fun phi : H.obj ⟶ (G' : X.Modules) =>
                phi ≫ Subobject.ofLE G' G hG'))

/- The universal-property witness is greatest among quasicoherent subobjects contained in
the prescribed subobject. -/
#check
  (AlgebraicGeometry.Scheme.Modules.isGreatest_of_quasiCoherent_hom_bijective :
    ∀ {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
      (G G' : Subobject F) (hG' : G' ≤ G)
      (_ : (G' : X.Modules).IsQuasicoherent)
      (_ : ∀ H : X.QCoh,
        Function.Bijective
          (fun phi : H.obj ⟶ (G' : X.Modules) =>
            phi ≫ Subobject.ofLE G' G hG')),
      IsGreatest {G'' : Subobject F | (G'' : X.Modules).IsQuasicoherent ∧ G'' ≤ G} G')
