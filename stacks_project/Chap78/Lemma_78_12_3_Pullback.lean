module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Pullback

/-! # Pullback of quasi-coherent modules on groupoids in algebraic spaces -/

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.pullback f : H.QCoh ⥤ G.QCoh)
