/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra

open AlgebraicGeometry

noncomputable section

universe u

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] (n : ℕ)

/- Definition 31.19.1: For an immersion `f : Z ⟶ X`, the conormal algebra is the
quasi-coherent `ℕ`-graded `𝒪_Z`-algebra with degree-`n` piece `𝓘 ^ n / 𝓘 ^ (n + 1)`. -/
@[stacks 0630] #check (AlgebraicGeometry.Scheme.ConormalAlgebra f :
  SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} Z.sheaf ℕ)

#check (AlgebraicGeometry.Scheme.ConormalAlgebra.pieceIso f n :
  (AlgebraicGeometry.Scheme.ConormalAlgebra f).obj n ≅
    SheafOfModules.RingedSite.KernelIdeal.AssociatedGraded.pieceSheaf.{u, u}
      (AlgebraicGeometry.RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom) n)

#check (AlgebraicGeometry.Scheme.ConormalAlgebra.isQuasicoherent f :
  (AlgebraicGeometry.Scheme.ConormalAlgebra f).IsQuasicoherent)

#check (AlgebraicGeometry.Scheme.ConormalAlgebra.instIsQuasicoherentObj f n :
  ((AlgebraicGeometry.Scheme.ConormalAlgebra f).obj n).IsQuasicoherent)
