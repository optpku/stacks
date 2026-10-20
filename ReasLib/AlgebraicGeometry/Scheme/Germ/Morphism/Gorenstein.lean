/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.RingTheory.Gorenstein.Local

/-!
# Fibre-stalk Gorenstein property of morphisms of scheme germs

The local ring of the fibre at the distinguished source point is a Gorenstein
local ring exactly when any representative has that property. This property
is invariant under étale localization on source and target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

/-- A morphism of scheme germs has Gorenstein fibre stalk if some representative
has Gorenstein local ring of the fibre at the distinguished source point. -/
def fiberStalkGorenstein : CategoryTheory.MorphismProperty Germ :=
  fun {X Y} f ↦
    ∃ r : Hom.Representative X Y,
      Hom.mk r = f ∧
        IsGorensteinLocalRing
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood))

/-- The fibre-stalk Gorenstein property of a germ morphism is witnessed by a
representative whose fibre stalk is a Gorenstein local ring. -/
theorem fiberStalkGorenstein_iff {X Y : Germ} (f : X ⟶ Y) :
    fiberStalkGorenstein f ↔
      ∃ r : Hom.Representative X Y,
        Hom.mk r = f ∧
          IsGorensteinLocalRing
            (Scheme.Hom.fiberStalkAt r.hom
              (X.pointIn r.neighborhood r.mem_neighborhood)) := Iff.rfl

/-- A represented germ morphism has Gorenstein fibre stalk exactly when the given
representative has Gorenstein fibre stalk. -/
theorem fiberStalkGorenstein_mk_iff {X Y : Germ} (r : Hom.Representative X Y) :
    fiberStalkGorenstein (Hom.mk r) ↔
      IsGorensteinLocalRing
        (Scheme.Hom.fiberStalkAt r.hom
          (X.pointIn r.neighborhood r.mem_neighborhood)) := sorry

/-- A represented germ morphism has Gorenstein fibre stalk exactly when the fibre
stalk of its representative is Noetherian and Gorenstein. -/
theorem fiberStalkGorenstein_spec {X Y : Germ} (r : Hom.Representative X Y) :
    fiberStalkGorenstein (Hom.mk r) ↔
      IsNoetherianRing
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood)) ∧
        IsGorensteinLocalRing
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood)) := sorry

/-- Having Gorenstein fibre stalk is étale local on the source and target for
morphisms of scheme germs. -/
theorem fiberStalkGorenstein_isEtaleLocal :
    IsEtaleLocal fiberStalkGorenstein := sorry

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
