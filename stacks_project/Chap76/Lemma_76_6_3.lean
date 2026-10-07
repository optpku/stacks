module

public import stacks_project.Chap76.Lemma_76_6_3_Map
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']
variable (sq : CommSq f i i' g)

/- Lemma 76.6.3: Let `S` be a scheme. A commutative diagram of algebraic spaces
over `S` whose horizontal arrows `i : Z ⟶ X` and `i' : Z' ⟶ X'` are immersions
induces a canonical morphism of graded `𝒪_Z`-algebras
`ConormalAlgebra.pullback f i' ⟶ ConormalAlgebra.total i`. -/
@[stacks 09RS]
#check
  (ConormalAlgebra.map sq :
    ConormalAlgebra.pullback f i' ⟶ ConormalAlgebra.total i)

#check (ConormalAlgebra.map_spec sq)
#check (ConormalAlgebra.mapPiece sq)
