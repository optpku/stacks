module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 65.7.3: let `S` be a scheme contained in `Sch_fppf`. Let `F ⟶ H`, `G ⟶ H` be
morphisms of algebraic spaces over `S`. Then `F ×_H G` is an algebraic space, and is a
fibre product in the category of algebraic spaces over `S`. -/
@[stacks 02X2] #check (AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.isPullback :
    ∀ {S : Scheme.{u}} {F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H),
      IsPullback
        (AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverFst
          f g H.isSheaf H.representableDiagonal)
        (AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverSnd
          f g H.isSheaf H.representableDiagonal) f g)

#check (AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.instHasPullbacks :
    ∀ {S : Scheme.{u}}, HasPullbacks (AlgebraicSpace S))
