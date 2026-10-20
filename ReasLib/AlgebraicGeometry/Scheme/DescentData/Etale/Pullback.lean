/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback

/-!
# Pullback of étale descent data

Pullback of singleton scheme descent data along a base change preserves the condition that
the unique component is étale.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Etale

variable {X S T : Scheme.{u}}

/-- Pulling an étale descent datum along `g : T ⟶ S` leaves its unique component étale
over the base-changed scheme `pullback f g`. -/
theorem baseChangeFunctor_mapsTo (f : X ⟶ S) (g : T ⟶ S) (D : Etale f) :
    etaleProperty (pullback.snd f g)
      ((forget f ⋙ Pullback.functor f (pullback.snd f g) g
        (pullback.fst f g) (CommSq.mk pullback.condition)).obj D) := sorry

/-- Pull back étale descent data along a morphism of base schemes. -/
noncomputable def baseChangeFunctor (f : X ⟶ S) (g : T ⟶ S) :
    Etale f ⥤ Etale (pullback.snd f g) :=
  (etaleProperty (pullback.snd f g)).lift
    (forget f ⋙ Pullback.functor f (pullback.snd f g) g
      (pullback.fst f g) (CommSq.mk pullback.condition))
    (baseChangeFunctor_mapsTo f g)

/-- Forgetting the étale condition on a base-changed datum recovers the ordinary pullback
of its underlying descent datum. -/
theorem baseChangeFunctor_obj (f : X ⟶ S) (g : T ⟶ S) (D : Etale f) :
    ((baseChangeFunctor f g).obj D).obj =
      (Pullback.functor f (pullback.snd f g) g
        (pullback.fst f g) (CommSq.mk pullback.condition)).obj D.obj := sorry

/-- The unique component of a base-changed étale descent datum is the pullback of the
original component along `pullback.fst f g`. -/
theorem baseChangeFunctor_obj_obj (f : X ⟶ S) (g : T ⟶ S) (D : Etale f) :
    ((baseChangeFunctor f g).obj D).obj.obj PUnit.unit =
      (Over.pullback (pullback.fst f g)).obj (D.obj.obj PUnit.unit) := sorry

end AlgebraicGeometry.Scheme.DescentData.Etale
