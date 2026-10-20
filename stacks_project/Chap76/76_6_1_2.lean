/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Grading
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- 76.6.1.2: For an immersion `i : Z ⟶ X` of algebraic spaces there is a canonical
surjective morphism of quasi-coherent graded `𝒪_Z`-algebras
`Sym^*(Hom.conormalSheaf i) ⟶ ConormalAlgebra.total i` which is an isomorphism in
degrees `0` and `1`. -/
@[stacks 09RQ] #check
  (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.symmetricToTotal i :
    ConormalAlgebra.symmetric i ⟶ ConormalAlgebra.total i)

#check (ConormalAlgebra.instIsLocallySurjective_symmetricToTotal i :
  Sheaf.IsLocallySurjective (ConormalAlgebra.symmetricToTotal i).hom.right)

#check (ConormalAlgebra.symmetricDegree i :
  ℕ → Subobject (SymmetricAlgebra.underlyingModule (Hom.conormalSheaf i)))
#check (ConormalAlgebra.totalDegree i :
  ℕ → Subobject (Modules.ofComm (ConormalAlgebra.totalUnderlyingModule i)))
#check ConormalAlgebra.symmetricDegree_isGrading i
#check ConormalAlgebra.totalDegree_isGrading i
#check ConormalAlgebra.symmetricToTotal_preservesDegree i
#check ConormalAlgebra.symmetricToTotalDegree_arrow i

#check (ConormalAlgebra.instIsIso_symmetricToTotalDegree_zero i :
  IsIso (ConormalAlgebra.symmetricToTotalDegree i 0))
#check (ConormalAlgebra.instIsIso_symmetricToTotalDegree_one i :
  IsIso (ConormalAlgebra.symmetricToTotalDegree i 1))
#check ConormalAlgebra.instIsQuasicoherent_symmetricDegree i
#check ConormalAlgebra.instIsQuasicoherent_totalDegree i
