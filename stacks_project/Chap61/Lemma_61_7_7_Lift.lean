/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Lift

@[expose] public section

open CategoryTheory

universe u

/-!
# Lifting ind-étale algebras along a quotient

The reusable factorization category, colimit construction, lift functor, and
quotient comparison are owned by `ReasLib.Algebra.Category.CommAlgCat.IndEtale.Lift`.
-/

/- The explicit factorization data used by the lifting construction. -/
#check (CommAlgCat.IndEtale.Factorization :
  ∀ (A T : Type u) [CommRing A] [CommRing T] [Algebra A T], Type u)

/- The lift functor is the right-adjoint candidate for reduction. -/
#check (CommAlgCat.IndEtale.lift :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    CommAlgCat.IndEtale.{u} (A ⧸ I) ⥤ CommAlgCat.IndEtale.{u} A)

/- The counit comparison is the quotient descent map. -/
#check (CommAlgCat.IndEtale.counitApp :
  ∀ {A : Type u} [CommRing A] (I : Ideal A)
    (Cbar : CommAlgCat.IndEtale.{u} (A ⧸ I)),
    (CommAlgCat.IndEtale.reduction I).obj
        ((CommAlgCat.IndEtale.lift I).obj Cbar) ⟶ Cbar)
