/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Diagonal
import StacksCheckRecall

/-!
# Representability of the diagonal of a presheaf by algebraic spaces

The diagonal of a presheaf on schemes over `S` is representable by algebraic
spaces if and only if every map from a scheme, equivalently from an algebraic
space, into that presheaf is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.5.1: the diagonal of an arbitrary presheaf is representable by
algebraic spaces if and only if every map from a scheme to it is representable
by algebraic spaces, equivalently every map from an algebraic space is. -/
@[stacks 03Y2] #check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.diag_iff :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
      representableByAlgebraicSpaces (diag F) ↔
        ∀ ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F), representableByAlgebraicSpaces a)

#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.diag_iff_isAlgebraicSpace :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
      representableByAlgebraicSpaces (diag F) ↔
        ∀ ⦃X : (Over S)ᵒᵖ ⥤ Type u⦄ [IsAlgebraicSpace X] (a : X ⟶ F),
          representableByAlgebraicSpaces a)

#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.of_diag :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
      representableByAlgebraicSpaces (diag F) →
        ∀ ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F), representableByAlgebraicSpaces a)

#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.of_diag_isAlgebraicSpace :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
      representableByAlgebraicSpaces (diag F) →
        ∀ ⦃X : (Over S)ᵒᵖ ⥤ Type u⦄ [IsAlgebraicSpace X] (a : X ⟶ F),
          representableByAlgebraicSpaces a)

#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.diag_of_yoneda :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
      (∀ ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F), representableByAlgebraicSpaces a) →
      representableByAlgebraicSpaces (diag F))

end AlgebraicGeometry.AlgebraicSpace
