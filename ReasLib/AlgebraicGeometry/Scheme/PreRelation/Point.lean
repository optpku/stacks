/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
import ReasLib.AlgebraicGeometry.Scheme.Pullback.Point

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- A pre-equivalence relation on a scheme induces an equivalence relation on its
underlying points, with related pairs witnessed by points of the pre-relation. -/
theorem pointRelIsEquivalence {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    (hP : P.IsPreEquivalence) :
    Equivalence (fun x y : U.left ↦
      ∃ r : P.left.left, P.t.left r = x ∧ P.s.left r = y) := by
  constructor
  · intro x
    let T : Over S := Over.mk (U.left.fromSpecResidueField x ≫ U.hom)
    let xOver : T ⟶ U := Over.homMk (U.left.fromSpecResidueField x)
    obtain ⟨r, hrt, hrs⟩ := (hP T).1 xOver
    let c := IsLocalRing.closedPoint (U.left.residueField x)
    have hx : xOver.left c = x := by
      change U.left.fromSpecResidueField x c = x
      exact Scheme.fromSpecResidueField_apply x c
    have hrt' : P.t.left (r.left c) = xOver.left c :=
      congrArg (fun f ↦ f.left c) hrt
    have hrs' : P.s.left (r.left c) = xOver.left c :=
      congrArg (fun f ↦ f.left c) hrs
    refine ⟨r.left c, ?_, ?_⟩
    · exact hrt'.trans hx
    · exact hrs'.trans hx
  · intro x y hxy
    rcases hxy with ⟨z, htz, hsz⟩
    let R := P.left.left
    let T : Over S := Over.mk (R.fromSpecResidueField z ≫ P.left.hom)
    let zOver : T ⟶ P.left := Over.homMk (R.fromSpecResidueField z)
    have hzy : P.pointRel T (zOver ≫ P.t) (zOver ≫ P.s) := ⟨zOver, rfl, rfl⟩
    obtain ⟨r, hrt, hrs⟩ := (hP T).symm hzy
    let c := IsLocalRing.closedPoint (R.residueField z)
    have hz : zOver.left c = z := by
      change R.fromSpecResidueField z c = z
      exact Scheme.fromSpecResidueField_apply z c
    have hrt' : P.t.left (r.left c) = P.s.left (zOver.left c) :=
      congrArg (fun f ↦ f.left c) hrt
    have hrs' : P.s.left (r.left c) = P.t.left (zOver.left c) :=
      congrArg (fun f ↦ f.left c) hrs
    refine ⟨r.left c, ?_, ?_⟩
    · calc
        P.t.left (r.left c) = P.s.left (zOver.left c) := hrt'
        _ = P.s.left z := by rw [hz]
        _ = y := hsz
    · calc
        P.s.left (r.left c) = P.t.left (zOver.left c) := hrs'
        _ = P.t.left z := by rw [hz]
        _ = x := htz
  · intro x y z hxy hyz
    rcases hxy with ⟨xy, hxyt, hxys⟩
    rcases hyz with ⟨yz, hyzt, hyzs⟩
    obtain ⟨w, hwfst, hwsnd⟩ :=
      (Scheme.Pullback.exists_point_iff P.s.left P.t.left xy yz).2 (hxys.trans hyzt.symm)
    let hw : Spec ((pullback P.s.left P.t.left : Scheme).residueField w) ⟶
        pullback P.s.left P.t.left := (pullback P.s.left P.t.left).fromSpecResidueField w
    let T : Over S := Over.mk
      (hw ≫ pullback.fst P.s.left P.t.left ≫ P.left.hom)
    let hwfstOver : T ⟶ P.left := Over.homMk (hw ≫ pullback.fst P.s.left P.t.left)
    let hwsndOver : T ⟶ P.left :=
      Over.homMk (hw ≫ pullback.snd P.s.left P.t.left) (by
        change hw ≫ pullback.snd P.s.left P.t.left ≫ P.left.hom =
          hw ≫ pullback.fst P.s.left P.t.left ≫ P.left.hom
        simpa [hw, Category.assoc] using
          congrArg (fun k ↦ hw ≫ k ≫ U.hom)
            (pullback.condition :
              pullback.fst P.s.left P.t.left ≫ P.s.left =
                pullback.snd P.s.left P.t.left ≫ P.t.left).symm)
    have hxy' : P.pointRel T (hwfstOver ≫ P.t) (hwfstOver ≫ P.s) := ⟨hwfstOver, rfl, rfl⟩
    have hyz' : P.pointRel T (hwfstOver ≫ P.s) (hwsndOver ≫ P.s) := by
      refine ⟨hwsndOver, ?_, rfl⟩
      ext
      change hw ≫ pullback.snd P.s.left P.t.left ≫ P.t.left =
        hw ≫ pullback.fst P.s.left P.t.left ≫ P.s.left
      simpa [hw, Category.assoc] using
        congrArg
          (fun k ↦ hw ≫ k)
          (pullback.condition :
            pullback.fst P.s.left P.t.left ≫ P.s.left =
              pullback.snd P.s.left P.t.left ≫ P.t.left).symm
    obtain ⟨r, hrt, hrs⟩ := (hP T).trans hxy' hyz'
    let c := IsLocalRing.closedPoint ((pullback P.s.left P.t.left : Scheme).residueField w)
    have hwc : hw c = w := by
      change (pullback P.s.left P.t.left).fromSpecResidueField w c = w
      exact Scheme.fromSpecResidueField_apply w c
    have hwfstOver_eq : hwfstOver.left c = xy := by
      change pullback.fst P.s.left P.t.left (hw c) = xy
      rw [hwc, hwfst]
    have hwsndOver_eq : hwsndOver.left c = yz := by
      change pullback.snd P.s.left P.t.left (hw c) = yz
      rw [hwc, hwsnd]
    have hrt' : P.t.left (r.left c) = P.t.left (hwfstOver.left c) :=
      congrArg (fun f ↦ f.left c) hrt
    have hrs' : P.s.left (r.left c) = P.s.left (hwsndOver.left c) :=
      congrArg (fun f ↦ f.left c) hrs
    refine ⟨r.left c, ?_, ?_⟩
    · calc
        P.t.left (r.left c) = P.t.left (hwfstOver.left c) := hrt'
        _ = P.t.left xy := by rw [hwfstOver_eq]
        _ = x := hxyt
    · calc
        P.s.left (r.left c) = P.s.left (hwsndOver.left c) := hrs'
        _ = P.s.left yz := by rw [hwsndOver_eq]
        _ = z := hyzs

end AlgebraicGeometry.Scheme.PreRelation
