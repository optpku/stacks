/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Affine

universe u

open CategoryTheory

variable {X Z : AlgebraicGeometry.Scheme.{u}}
  (i : Z ⟶ X) [AlgebraicGeometry.IsImmersion i] (n : ℕ)

/- Lemma 31.19.2 (1): the degree-`n` piece of the conormal algebra of an immersion is
canonically the sheafified scalar extension of the successive kernel-ideal quotient. -/
@[stacks 0633] #check
  (AlgebraicGeometry.Scheme.ConormalAlgebra.pieceIso i n :
    (AlgebraicGeometry.Scheme.ConormalAlgebra i).obj n ≅
      SheafOfModules.RingedSite.KernelIdeal.AssociatedGraded.pieceSheaf.{u, u}
        (AlgebraicGeometry.RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) n)

variable {R : Type u} [CommRing R] (I : Ideal R) (m : ℕ)

/- Lemma 31.19.2 (2): on the affine quotient chart `Spec(R ⧸ I) ⟶ Spec(R)`, the
canonical degree-`m` comparison from `I^m / I^(m + 1)` to conormal-algebra sections is an
isomorphism. -/
@[stacks 0633]
#check
  (AlgebraicGeometry.Scheme.Hom.Conormal.quotientMapAssociatedGradedToSections_isIso I m :
    IsIso
      (AlgebraicGeometry.Scheme.Hom.Conormal.quotientMapAssociatedGradedToSections I m))
