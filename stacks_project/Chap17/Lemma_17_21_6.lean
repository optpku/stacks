module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorAlgebra.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricAlgebra.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Exterior
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Symmetric
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open SheafOfModules
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

universe u

/- Lemma 17.21.6 (1) (01CL), tensor algebra: tensor algebras preserve quasi-coherence. -/
@[stacks 01CL "(1), tensor algebra"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsQuasicoherent] ↦
  (TensorAlgebra.isQuasicoherent F : (T(F)).IsQuasicoherent)

/- Lemma 17.21.6 (1) (01CL), exterior algebra: exterior algebras preserve quasi-coherence. -/
@[stacks 01CL "(1), exterior algebra"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsQuasicoherent] ↦
  (ExteriorAlgebra.isQuasicoherent F : (Λ(F)).IsQuasicoherent)

/- Lemma 17.21.6 (1) (01CL), symmetric algebra: symmetric algebras preserve quasi-coherence. -/
@[stacks 01CL "(1), symmetric algebra"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsQuasicoherent] ↦
  (SymmetricAlgebra.isQuasicoherent F : (Symm(F)).IsQuasicoherent)

/- Lemma 17.21.6 (2) (01CL), tensor algebra: tensor algebras preserve local freeness. -/
@[stacks 01CL "(2), tensor algebra"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsLocallyFree] ↦
  (TensorAlgebra.isLocallyFree F : (T(F)).IsLocallyFree)

/- Lemma 17.21.6 (2) (01CL), exterior algebra: exterior algebras preserve local freeness. -/
@[stacks 01CL "(2), exterior algebra"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsLocallyFree] ↦
  (ExteriorAlgebra.isLocallyFree F : (Λ(F)).IsLocallyFree)

/- Lemma 17.21.6 (2) (01CL), symmetric algebra: symmetric algebras preserve local freeness. -/
@[stacks 01CL "(2), symmetric algebra"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsLocallyFree] ↦
  (SymmetricAlgebra.isLocallyFree F : (Symm(F)).IsLocallyFree)
