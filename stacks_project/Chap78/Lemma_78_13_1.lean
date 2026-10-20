module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Coinduction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

/- Lemma 78.13.1: for a groupoid in algebraic spaces whose source and target are
flat, quasi-compact, and quasi-separated, coinduction on quasi-coherent modules is
right adjoint to forgetting equivariance. -/
@[stacks 0GPP] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.forgetCoinductionAdjunction :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
      [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left],
      forget G ⊣ coinduction G)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.coinduction_obj_obj :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
      [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]
      (F : AlgebraicSpace.QCoh G.U.left),
      ((coinduction G).obj F).obj =
        (AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pushforward G.s.left).obj F)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.coinduction_action :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
      [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]
      (F : AlgebraicSpace.QCoh G.U.left),
      ((coinduction G).obj F).action = coinductionAction G F)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.coinductionAction_isIso :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
      [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]
      (F : AlgebraicSpace.QCoh G.U.left),
      IsIso (coinductionAction G F))

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
