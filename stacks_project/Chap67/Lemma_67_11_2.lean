module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 67.11.2: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. If `f` is quasi-compact and quasi-separated, then `f_*` transforms quasi-coherent
`𝒪_X`-modules into quasi-coherent `𝒪_Y`-modules. -/
@[stacks 03M9]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward.isQuasicoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f]
    (F : AlgebraicGeometry.AlgebraicSpace.Modules X) [F.IsQuasicoherent],
    ((AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f).obj F).IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f],
    AlgebraicGeometry.AlgebraicSpace.QCoh X ⥤ AlgebraicGeometry.AlgebraicSpace.QCoh Y)
