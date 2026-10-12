/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.CohenMacaulay

/-!
# Cohen--Macaulay fibre stalks of morphisms of scheme germs

This file checks the property of a morphism of scheme germs that the local ring
of the fibre at the distinguished source point is Noetherian and Cohen--Macaulay.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

#check (fiberStalkCohenMacaulay : CategoryTheory.MorphismProperty Germ.{u})
#check (fiberStalkCohenMacaulay_iff : ∀ {X Y : Germ.{u}} (f : X ⟶ Y),
  fiberStalkCohenMacaulay f ↔
    ∃ r : Hom.Representative X Y, Hom.mk r = f ∧
      CohenMacaulayRing
        (Scheme.Hom.fiberStalkAt r.hom (X.pointIn r.neighborhood r.mem_neighborhood)))
#check (fiberStalkCohenMacaulay_mk_iff : ∀ {X Y : Germ.{u}} (r : Hom.Representative X Y),
  fiberStalkCohenMacaulay (Hom.mk r) ↔
    CohenMacaulayRing
      (Scheme.Hom.fiberStalkAt r.hom (X.pointIn r.neighborhood r.mem_neighborhood)))
#check (fiberStalkCohenMacaulay_mk_spec : ∀ {X Y : Germ.{u}} (r : Hom.Representative X Y),
  fiberStalkCohenMacaulay (Hom.mk r) ↔
    IsNoetherianRing
      (Scheme.Hom.fiberStalkAt r.hom (X.pointIn r.neighborhood r.mem_neighborhood)) ∧
    CohenMacaulayRing
      (Scheme.Hom.fiberStalkAt r.hom (X.pointIn r.neighborhood r.mem_neighborhood)))

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
