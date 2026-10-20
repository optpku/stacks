/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.Gorenstein

/-!
# Fibre-stalk Gorenstein property of morphisms of scheme germs

This file records the property that the local ring of the fibre at the
distinguished source point is a Gorenstein local ring, and records its
invariance under étale localization on source and target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

#check (fiberStalkGorenstein : CategoryTheory.MorphismProperty Germ.{u})

#check (fiberStalkGorenstein_iff : ∀ {X Y : Germ.{u}} (f : X ⟶ Y),
    fiberStalkGorenstein f ↔
      ∃ r : Hom.Representative X Y,
        Hom.mk r = f ∧
          IsGorensteinLocalRing
            (Scheme.Hom.fiberStalkAt r.hom
              (X.pointIn r.neighborhood r.mem_neighborhood)))

#check (fiberStalkGorenstein_mk_iff :
    ∀ {X Y : Germ.{u}} (r : Hom.Representative X Y),
    fiberStalkGorenstein (Hom.mk r) ↔
      IsGorensteinLocalRing
        (Scheme.Hom.fiberStalkAt r.hom
          (X.pointIn r.neighborhood r.mem_neighborhood)))

#check (fiberStalkGorenstein_spec :
    ∀ {X Y : Germ.{u}} (r : Hom.Representative X Y),
    fiberStalkGorenstein (Hom.mk r) ↔
      IsNoetherianRing
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood)) ∧
        IsGorensteinLocalRing
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood)))

#check (fiberStalkGorenstein_isEtaleLocal :
    IsEtaleLocal (fiberStalkGorenstein : CategoryTheory.MorphismProperty Germ.{u}))

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
