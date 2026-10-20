module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
  (F : Modules X) [F.IsQuasicoherent]

/- Definition 69.12.1: let `S` be a scheme and let `X` be a locally Noetherian algebraic space
over `S`. A quasi-coherent module `F` on `X` is called coherent if `F` is a coherent
`𝒪_X`-module on the small étale site of `X` in the sense of `SheafOfModules.IsCoherent`. -/
@[stacks 07UA]
#check (SheafOfModules.IsCoherent
  (R := AlgebraicGeometry.AlgebraicSpace.structureSheaf X) F : Prop)
