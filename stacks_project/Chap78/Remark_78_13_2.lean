module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Coinduction.Unit
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

/- Remark 78.13.2: in the situation of Lemma 78.13.1, the underlying morphism of the
unit of the forgetful–coinduction adjunction at `A` is the pullback–pushforward unit
along `G.s.left` followed by the pushforward of `actionInverse A`. -/
@[stacks 0GPQ] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.forgetCoinductionAdjunction_unit_app_hom :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
      [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]
      (A : G.QCoh),
      hom ((forgetCoinductionAdjunction G).unit.app A) =
        (AlgebraicSpace.quasiCoherentModuleProperty G.U.left).homMk
          ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction G.s.left).homEquiv A.obj.obj
            ((AlgebraicSpace.Modules.pullback G.t.left).obj A.obj.obj) (actionInverse A).hom))

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
