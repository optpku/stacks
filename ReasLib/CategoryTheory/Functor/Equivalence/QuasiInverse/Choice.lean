/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Adjointification

/-!
# Choice independence of explicit quasi-inverses

This leaf owns the canonical isomorphism between inverse functors carried by two explicit
quasi-inverses, its groupoid laws, and compatibility with the retained counit and the
adjointified unit.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.Functor.QuasiInverse

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {F : A ⥤ B}

/-- The inverse functors carried by two explicit quasi-inverses of the same functor are naturally
isomorphic. This is the neutral choice-independence owner for constructions using explicit
quasi-inverse data. -/
def inverseIso (e e' : QuasiInverse F) : e.inverse ≅ e'.inverse :=
  Iso.isoInverseOfIsoFunctor
    (G := e.adjointifyUnit) (G' := e'.adjointifyUnit) (Iso.refl F)

/-- Comparing an explicit quasi-inverse with itself gives the identity inverse-functor
isomorphism. -/
@[simp]
theorem inverseIso.refl (e : QuasiInverse F) :
    e.inverseIso e = Iso.refl e.inverse := sorry

/-- Reversing the canonical inverse-functor comparison exchanges the two quasi-inverses. -/
@[simp]
theorem inverseIso.symm (e e' : QuasiInverse F) :
    (e.inverseIso e').symm = e'.inverseIso e := sorry

/-- Canonical inverse-functor comparisons compose transitively. -/
theorem inverseIso.trans (e e' e'' : QuasiInverse F) :
    e.inverseIso e' ≪≫ e'.inverseIso e'' = e.inverseIso e'' := sorry

/-- The canonical inverse-functor comparison intertwines the retained counits of the two
quasi-inverses. -/
theorem inverseIso.counit (e e' : QuasiInverse F) :
    Functor.isoWhiskerRight (e.inverseIso e') F ≪≫ e'.counitIso =
      e.counitIso := sorry

/-- The forward inverse-functor comparison intertwines the retained counits objectwise. -/
theorem inverseIso.hom.counit_app (e e' : QuasiInverse F) (X : B) :
    F.map ((e.inverseIso e').hom.app X) ≫ e'.counitIso.hom.app X =
      e.counitIso.hom.app X := sorry

/-- The inverse inverse-functor comparison intertwines the retained counits objectwise. -/
theorem inverseIso.inv.counit_app (e e' : QuasiInverse F) (X : B) :
    e'.counitIso.inv.app X ≫ F.map ((e.inverseIso e').inv.app X) =
      e.counitIso.inv.app X := sorry

/-- The canonical inverse-functor comparison also intertwines the adjointified units. The raw
supplied units need not satisfy this equation, which is why the statement uses
`adjointifyUnit`. -/
theorem inverseIso.adjointifyUnit (e e' : QuasiInverse F) :
    e.adjointifyUnit.unitIso ≪≫
        Functor.isoWhiskerLeft F (e.inverseIso e') =
      e'.adjointifyUnit.unitIso := sorry

/-- The forward inverse-functor comparison intertwines the adjointified units objectwise. -/
theorem inverseIso.hom.adjointifyUnit_app (e e' : QuasiInverse F) (X : A) :
    e.adjointifyUnit.unitIso.hom.app X ≫
        (e.inverseIso e').hom.app (F.obj X) =
      e'.adjointifyUnit.unitIso.hom.app X := sorry

/- Axiom audit: `inverseIso` is mathlib's canonical inverse comparison for two explicit
equivalences with the same forward functor; theorem-valued coherence carries the statement-stage
proof debt. -/

end CategoryTheory.Functor.QuasiInverse
