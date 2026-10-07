module

public import stacks_project.Chap78.Lemma_78_13_1_Coinduction

/-!
# Unit of the forgetful–coinduction adjunction
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable (G : GroupoidAlgebraicSpace B)
variable [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
variable [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
variable [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]

/-- The underlying morphism of the unit of the forgetful–coinduction adjunction is the
pullback–pushforward unit along the source followed by pushforward of the inverse action. -/
theorem forgetCoinductionAdjunction_unit_app_hom (A : G.QCoh) :
    hom ((forgetCoinductionAdjunction G).unit.app A) =
      (AlgebraicSpace.quasiCoherentModuleProperty G.U.left).homMk
        ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction G.s.left).homEquiv A.obj.obj
          ((AlgebraicSpace.Modules.pullback G.t.left).obj A.obj.obj) (actionInverse A).hom) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
