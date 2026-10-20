module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Coinduction.Unit
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/- Remark 39.15.2: the underlying morphism of the unit of the
forgetful–coinduction adjunction at `A` is the pullback–pushforward unit followed by
the pushforward of the inverse of `A.action`. -/
@[stacks 0GNF] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.forgetCoinductionAdjunction_unit_app_hom :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [Flat G.s.left] [Flat G.t.left]
      [QuasiCompact G.s.left] [QuasiCompact G.t.left]
      [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
      (A : G.QCoh),
      hom ((forgetCoinductionAdjunction G).unit.app A) =
        (Scheme.QCoh.pullbackPushforwardAdjunction G.s.left).unit.app A.obj ≫
          (Scheme.QCoh.pushforward G.s.left).map (actionInverse A))

end AlgebraicGeometry.GroupoidScheme.QCoh
