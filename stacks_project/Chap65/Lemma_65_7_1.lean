module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

variable {S : Scheme.{u}} (F G : AlgebraicSpace S)

/- Lemma 65.7.1 (1): let `S` be a scheme contained in `Sch_fppf`. Let `F`, `G` be
algebraic spaces over `S`. Then `F × G` is an algebraic space. -/
@[stacks 02X0]
#check (AlgebraicGeometry.AlgebraicSpace.product F G : AlgebraicSpace S)

/- Lemma 65.7.1 (2): the sheaf product `F × G` is a product in the category of
algebraic spaces over `S`. -/
@[stacks 02X0]
#check (AlgebraicGeometry.AlgebraicSpace.product_isLimit F G :
  IsLimit (BinaryFan.mk (AlgebraicSpace.productFst F G) (AlgebraicSpace.productSnd F G)))
