module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Module.Quasicoherent.Pullback
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)

/- Lemma 78.10.2: Let `B → S` as in Section 78.3. Let `G` be a group algebraic space
over `B`. Let `f : X ⟶ Y` be a `G`-equivariant morphism between algebraic spaces over
`B` endowed with `G`-actions. Then pullback `f*` given by
`(F, α) ↦ (f* F, (1_G × f)* α)` defines a functor from the category of quasi-coherent
`G`-equivariant sheaves on `Y` to the category of quasi-coherent `G`-equivariant sheaves
on `X`. -/
@[stacks 043U] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.pullback G f :
    AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant G Y ⥤
      AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant G X)
