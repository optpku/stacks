module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Coinduction

/-!
# Unit of the forgetful–coinduction adjunction
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

variable {S : Scheme.{u}}

/-- The underlying morphism of the unit of the forgetful–coinduction adjunction is the
pullback–pushforward unit along the source followed by pushforward of the inverse action. -/
theorem forgetCoinductionAdjunction_unit_app_hom (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (A : G.QCoh) :
    hom ((forgetCoinductionAdjunction G).unit.app A) =
      (Scheme.QCoh.pullbackPushforwardAdjunction G.s.left).unit.app A.obj ≫
        (Scheme.QCoh.pushforward G.s.left).map (actionInverse A) := sorry

end AlgebraicGeometry.GroupoidScheme.QCoh
