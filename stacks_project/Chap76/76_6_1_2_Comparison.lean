/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Symmetric

/-!
# Symmetric-to-total comparison for conormal algebras of immersions

The degree-one classes induce the canonical morphism from the symmetric algebra
of the conormal sheaf to the total conormal algebra.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.symmetricToTotal i :
  ConormalAlgebra.symmetric i ⟶ ConormalAlgebra.total i)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.symmetric_obj i :
  (ConormalAlgebra.symmetric i).obj = SymmetricAlgebra.under (Hom.conormalSheaf i))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.symmetric_sheaf i :
  (ConormalAlgebra.symmetric i).obj.right = SymmetricAlgebra.sheaf (Hom.conormalSheaf i))

#check
  (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.instIsLocallySurjective_symmetricToTotal i :
    Sheaf.IsLocallySurjective (ConormalAlgebra.symmetricToTotal i).hom.right)
