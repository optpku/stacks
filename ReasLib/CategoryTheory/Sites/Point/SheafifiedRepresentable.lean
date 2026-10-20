/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom

/-!
# Point fibers of sheafified representables

This module provides the canonical generators of the point fiber of a
sheafified representable and the fine-grained stalkwise comparison API they
induce.  It is independent of Chapter 7 and is intended for any argument that
tests morphisms of sheaves at points.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

universe w v u w'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The canonical generator of the point fiber of `uliftYoneda.obj U` associated to
`x : q.fiber.obj U`. -/
noncomputable abbrev uliftYonedaGenerator
    (q : GrothendieckTopology.Point.{w'} J) (U : C) :
    q.fiber.obj U →
      q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) :=
  fun x ↦
    q.toPresheafFiber U x (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
      (ULift.up (𝟙 U))

/-- The Yoneda generators indexed by `q.fiber.obj U` jointly cover the point fiber of
`uliftYoneda.obj U`. -/
lemma uliftYonedaGenerator_surjective
    (q : GrothendieckTopology.Point.{w'} J) (U : C) :
    Function.Surjective (uliftYonedaGenerator (q := q) U) := sorry

namespace SheafifiedRepresentable

/-- The canonical element of the stalk of the sheafified representable associated to
`x : q.fiber.obj U`. -/
noncomputable def stalkElement
    [HasWeakSheafify J (Type (max u v w'))]
    (q : GrothendieckTopology.Point.{w'} J) (U : C) (x : q.fiber.obj U) :
    (q.sheafFiber (A := Type (max u v w'))).obj
      (J.uliftSheafifiedRepresentable.{max u v w', v, u} U) :=
  (q.presheafFiber (A := Type (max u v w'))).map
      (CategoryTheory.toSheafify J
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U))
    (uliftYonedaGenerator (q := q) U x)

/-- The canonical stalk elements indexed by `q.fiber.obj U` jointly cover the stalk of the
sheafified representable at `U`. -/
lemma stalkElement_surjective
    [HasWeakSheafify J (Type (max u v w'))]
    (q : GrothendieckTopology.Point.{w'} J) (U : C) :
    Function.Surjective (stalkElement (q := q) U) := sorry

/-- Evaluating a morphism out of a sheafified representable on a canonical stalk element gives
the germ of the corresponding represented section. -/
lemma stalkMap_apply
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : GrothendieckTopology.Point.{w'} J) (U : C)
    (alpha : J.uliftSheafifiedRepresentable.{max u v w', v, u} U ⟶ ℱ)
    (x : q.fiber.obj U) :
    (q.sheafFiber (A := Type (max u v w'))).map alpha (stalkElement (q := q) U x) =
      q.toPresheafFiber U x ℱ.obj
        (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv
          J ℱ U alpha) := sorry

/-- Two maps out of a sheafified representable agree on a canonical stalk element exactly when
their corresponding represented sections have the same germ there. -/
lemma stalkMap_eq_iff
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : GrothendieckTopology.Point.{w'} J) (U : C)
    (alpha beta : J.uliftSheafifiedRepresentable.{max u v w', v, u} U ⟶ ℱ)
    (x : q.fiber.obj U) :
    (q.sheafFiber (A := Type (max u v w'))).map alpha (stalkElement (q := q) U x) =
      (q.sheafFiber (A := Type (max u v w'))).map beta (stalkElement (q := q) U x) ↔
      q.toPresheafFiber U x ℱ.obj
          (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv
            J ℱ U alpha) =
        q.toPresheafFiber U x ℱ.obj
          (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv
            J ℱ U beta) := sorry

/-- Equality of the represented germs over `U` forces equality of the induced stalk maps out of
the sheafified representable. -/
lemma stalkMap_ext_of_pointwiseGermEq
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : GrothendieckTopology.Point.{w'} J) (U : C)
    (alpha beta : J.uliftSheafifiedRepresentable.{max u v w', v, u} U ⟶ ℱ)
    (h :
      ∀ x : q.fiber.obj U,
        q.toPresheafFiber U x ℱ.obj
            (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv
              J ℱ U alpha) =
          q.toPresheafFiber U x ℱ.obj
            (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv
              J ℱ U beta)) :
    (q.sheafFiber (A := Type (max u v w'))).map alpha =
      (q.sheafFiber (A := Type (max u v w'))).map beta := sorry

end SheafifiedRepresentable

end CategoryTheory.GrothendieckTopology.Point
