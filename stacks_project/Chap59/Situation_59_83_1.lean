module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable (h_dimension : topologicalKrullDim X.left ≤ 1)
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
variable (hF : CategoryTheory.Sheaf.IsLocallyTorsion F)

#check (inferInstance : Field k)
#check (inferInstance : IsAlgClosed k)
#check (X : AlgebraicGeometry.SchemeOverField k)
#check (inferInstance : Scheme.Hom.FiniteType X.hom)
#check (inferInstance : IsSeparated X.hom)
#check (h_dimension : topologicalKrullDim X.left ≤ 1)
#check (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
#check (hF : CategoryTheory.Sheaf.IsLocallyTorsion F)

/- Situation 59.83.1: The surrounding variables fix an algebraically closed field `k`,
a separated finite-type scheme `X` over `k` of dimension at most `1`, and an abelian
sheaf `F` on `X.left.smallEtaleTopology` with the local torsion assumption `hF`.
The predicate check identifies this torsion notion; it does not assert that arbitrary
sheaves are torsion. -/
@[stacks 0A52] #check (CategoryTheory.Sheaf.IsLocallyTorsion :
  Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} → Prop)

end
