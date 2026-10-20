/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y X' Y' : Scheme.{u}}

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (square : CommSq g' f' f g)
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/- 59.91.5.3: for E = F[0], the canonical derived comparison specializes to
the usual sheaf notation g⁻¹Rf_*F ⟶ Rf'_*(g')⁻¹F. -/
@[stacks 0A4A] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq f g f' g' square
    ((DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) :
    (Derived.inverseImage g).obj
        ((Derived.directImage f).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ⟶
      (Derived.directImage f').obj
        ((Derived.inverseImage g').obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))
