module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Coinduction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/- Lemma 39.15.1: for a groupoid scheme whose source and target are flat,
quasi-compact, and quasi-separated, coinduction on quasi-coherent modules is
right adjoint to forgetting equivariance. -/
@[stacks 07TR] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.forgetCoinductionAdjunction :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [Flat G.s.left] [Flat G.t.left]
      [QuasiCompact G.s.left] [QuasiCompact G.t.left]
      [QuasiSeparated G.s.left] [QuasiSeparated G.t.left],
      forget G ⊣ coinduction G)

#check
  (AlgebraicGeometry.GroupoidScheme.QCoh.coinduction_obj_obj :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [Flat G.s.left] [Flat G.t.left]
      [QuasiCompact G.s.left] [QuasiCompact G.t.left]
      [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
      (F : Scheme.QCoh G.U.left),
      ((coinduction G).obj F).obj =
        (Scheme.QCoh.pullback G.t.left ⋙ Scheme.QCoh.pushforward G.s.left).obj F)

#check
  (AlgebraicGeometry.GroupoidScheme.QCoh.coinduction_action :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [Flat G.s.left] [Flat G.t.left]
      [QuasiCompact G.s.left] [QuasiCompact G.t.left]
      [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
      (F : Scheme.QCoh G.U.left),
      ((coinduction G).obj F).action = coinductionAction G F)

#check
  (AlgebraicGeometry.GroupoidScheme.QCoh.coinductionAction_isIso :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [Flat G.s.left] [Flat G.t.left]
      [QuasiCompact G.s.left] [QuasiCompact G.t.left]
      [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
      (F : Scheme.QCoh G.U.left),
      IsIso (coinductionAction G F))

end AlgebraicGeometry.GroupoidScheme.QCoh
