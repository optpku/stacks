module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Reduced
import StacksCheckRecall

/-!
# Reducedness of étale local rings

Source bridge: the reducedness comparison theorems are owned by the shared
ReasLib étale-local-ring module and are re-checked here against their source types.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.22.6 -/
@[stacks 0E01] #check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_isReduced_tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X), List.TFAE
    [localRingHas (fun R ↦ _root_.IsReduced R) X x,
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ _root_.IsReduced (etaleLocalRing X xbar),
      ∀ xbar : GeometricPoint X, xbar.liesOver x → _root_.IsReduced (etaleLocalRing X xbar)])

#check (AlgebraicGeometry.AlgebraicSpace.localRingHas_isReduced_iff_exists_etaleLocalRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    localRingHas (fun R ↦ _root_.IsReduced R) X x ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ _root_.IsReduced (etaleLocalRing X xbar))

#check (AlgebraicGeometry.AlgebraicSpace.localRingHas_isReduced_iff_forall_etaleLocalRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    localRingHas (fun R ↦ _root_.IsReduced R) X x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x → _root_.IsReduced (etaleLocalRing X xbar))

end AlgebraicGeometry.AlgebraicSpace
