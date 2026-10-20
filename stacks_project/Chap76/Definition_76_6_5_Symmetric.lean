module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SymmetricAlgebra

/-!
# Symmetric algebras of quasi-coherent modules on algebraic spaces

The sectionwise symmetric algebra of a quasi-coherent module sheaf on the small
étale site is a quasi-coherent algebra over the structure sheaf.
-/

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (F : X.Modules) [F.IsQuasicoherent]

#check (AlgebraicGeometry.AlgebraicSpace.SymmetricAlgebra.qcAlgebra F : X.QcAlgebraUnder)

#check (AlgebraicGeometry.AlgebraicSpace.SymmetricAlgebra.qcAlgebra_obj F :
  (SymmetricAlgebra.qcAlgebra F).obj = SymmetricAlgebra.under F)

#check (AlgebraicGeometry.AlgebraicSpace.SymmetricAlgebra.qcAlgebra_sheaf F :
  (SymmetricAlgebra.qcAlgebra F).obj.right = SymmetricAlgebra.sheaf F)

variable (A : X.QcAlgebraUnder)
variable (f : Modules.toComm F ⟶
  (restrictionAlong A.obj.hom).obj
    (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A)))

#check (AlgebraicGeometry.AlgebraicSpace.SymmetricAlgebra.lift F A f :
  SymmetricAlgebra.qcAlgebra F ⟶ A)
