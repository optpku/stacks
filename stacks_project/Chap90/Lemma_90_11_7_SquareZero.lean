/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero

/-!
# Trivial square-zero extensions as objects of `S`-Alg/`R`

The assignment `M ↦ R[M]` is the functor `ModuleCat R ⥤ Over (CommAlgCat.of S R)`
sending an `R`-module to the trivial square-zero extension `TrivSqZeroExt R M`,
viewed as an `S`-algebra over `R` via the canonical projection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TrivSqZeroExt

variable (S : Type u) [CommRing S]

/-- Typecheck an `S`-algebra homomorphism as a morphism in `CommAlgCat S`. -/
def homOfAlgHom {X Y : Type u} [CommRing X] [Algebra S X] [CommRing Y] [Algebra S Y]
    (f : X →ₐ[S] Y) : CommAlgCat.of S X ⟶ CommAlgCat.of S Y :=
  CommAlgCat.ofHom f

end TrivSqZeroExt
