/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorAlgebra.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricAlgebra.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Symmetric
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Exterior
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower.Graded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Sequence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower.Graded.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Sequence

/-!
# Algebra constructions on module sheaves

Stable entry point for the canonical sectionwise tensor, symmetric, and exterior algebra
presheaves, their sheafified module sheaves, the three standard power constructions, and the
exterior/symmetric power sequences. The standard local-property instances are re-exported from
their generic ringed-site owners, without a second ringed-space theorem layer. Stalk and pullback
comparisons are deliberately separate leaves, imported as
`AlgebraSheaf.Stalk` and `AlgebraSheaf.Pullback`; none of these owners depends on a chapter-local
presentation.
-/
@[expose] public section

