module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 70.9.1: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Every quasi-coherent `𝒪_X`-module is a filtered colimit of finitely presented
`𝒪_X`-modules. -/
@[stacks 07V9] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isFinitePresentation_ind_of_qcqs :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsQuasicoherent],
      (SheafOfModules.isFinitePresentation (structureSheaf X)).ind.{u} F)
