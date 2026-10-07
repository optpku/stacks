module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap69.Definition_69_12_1_Instances
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
#check (F.IsCoherent : Prop)
