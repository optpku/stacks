module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FinitePresentation.FilteredColimit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.15.2: let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of algebraic spaces
over `S` with `Y` Noetherian. Then every quasi-coherent `𝒪_X`-module is a filtered colimit of
finitely presented `𝒪_X`-modules. -/
@[stacks 07UW] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isFinitePresentation_ind :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f] [IsNoetherian Y]
      (F : X.Modules) [F.IsQuasicoherent],
      (SheafOfModules.isFinitePresentation (structureSheaf X)).ind.{u} F)
