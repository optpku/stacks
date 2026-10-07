module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Cofinal.Surjectivity
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.7 (01EU): cofinal vanishing of first Cech cohomology of the left term of a short
exact sequence makes the map on sections over the chosen open surjective. -/
@[stacks 01EU]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.VanishesCofinally.surjective_right

#check @AlgebraicGeometry.RingedSpace.ModuleCech.VanishesCofinally
#check @CategoryTheory.Sheaf.Cech.VanishesCofinally.surjective_right
