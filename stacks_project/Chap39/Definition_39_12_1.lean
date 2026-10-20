module

public import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable (S : Scheme.{u}) (G : Grp (Over S)) (X : GroupScheme.Action G)

/- Definition 39.12.1: The objects of `Scheme.QCoh.Equivariant G X` are
quasi-coherent modules `F` on `X` equipped with a linearization
`action G X`-pullback of `F` ⟶ `projection G X`-pullback of `F` satisfying
the cocycle and unit laws. -/
@[stacks 03LF] #check (AlgebraicGeometry.Scheme.QCoh.Equivariant G X : Cat)

/- Companion recall: equivariant quasi-coherent modules are built from a
quasi-coherent module, a linearization, and the cocycle and unit laws. -/
#check Scheme.QCoh.Equivariant.of

/- Companion recall: `obj`, `alpha`, `cocycle`, and `unit` recover the
underlying module, its linearization, and the two defining laws. -/
#check Scheme.QCoh.Equivariant.obj
#check Scheme.QCoh.Equivariant.alpha
#check Scheme.QCoh.Equivariant.cocycle
#check Scheme.QCoh.Equivariant.unit
