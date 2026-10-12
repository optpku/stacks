/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ
namespace MorphismProperty

/-- A morphism of scheme germs has a Cohen--Macaulay fibre stalk if this holds for
one representative at its distinguished source point. -/
def fiberStalkCohenMacaulay : CategoryTheory.MorphismProperty Germ.{u} :=
  fun {X Y} f ↦
    ∃ r : Hom.Representative X Y,
      Hom.mk r = f ∧
        CohenMacaulayRing
          (Scheme.Hom.fiberStalkAt r.hom (X.pointIn r.neighborhood r.mem_neighborhood))

/-- A germ morphism has a Cohen--Macaulay fibre stalk exactly when some representative
has a Cohen--Macaulay fibre stalk at the distinguished source point. -/
theorem fiberStalkCohenMacaulay_iff {X Y : Germ.{u}} (f : X ⟶ Y) :
    fiberStalkCohenMacaulay f ↔
      ∃ r : Hom.Representative X Y,
        Hom.mk r = f ∧
          CohenMacaulayRing
            (Scheme.Hom.fiberStalkAt r.hom
              (X.pointIn r.neighborhood r.mem_neighborhood)) := sorry

/-- A represented germ morphism has a Cohen--Macaulay fibre stalk exactly when its
given representative has a Cohen--Macaulay fibre stalk. -/
theorem fiberStalkCohenMacaulay_mk_iff {X Y : Germ.{u}}
    (r : Hom.Representative X Y) :
    fiberStalkCohenMacaulay (Hom.mk r) ↔
      CohenMacaulayRing
        (Scheme.Hom.fiberStalkAt r.hom
          (X.pointIn r.neighborhood r.mem_neighborhood)) := sorry

/-- A represented germ morphism has a Cohen--Macaulay fibre stalk exactly when that
fibre stalk is Noetherian and Cohen--Macaulay. -/
theorem fiberStalkCohenMacaulay_mk_spec {X Y : Germ.{u}}
    (r : Hom.Representative X Y) :
    fiberStalkCohenMacaulay (Hom.mk r) ↔
      IsNoetherianRing
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood)) ∧
        CohenMacaulayRing
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood)) := sorry

/-- The Cohen--Macaulay fibre-stalk property of morphisms of scheme germs is étale
local on the source and target. -/
theorem fiberStalkCohenMacaulay_isEtaleLocal :
    IsEtaleLocal fiberStalkCohenMacaulay := sorry

end MorphismProperty
end AlgebraicGeometry.Scheme.Germ
