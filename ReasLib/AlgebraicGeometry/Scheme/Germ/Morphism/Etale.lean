/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Category
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Germ

/-- A morphism of scheme germs is étale when it has a representative that is étale at the
distinguished source point. -/
class Etale {X Y : Germ} (f : X ⟶ Y) : Prop where
  /-- An étale representative of the germ morphism. -/
  exists_representation :
    ∃ r : Hom.Representative X Y,
      Hom.mk r = f ∧ r.hom.EtaleAt (X.pointIn r.neighborhood r.mem_neighborhood)

namespace Etale

/-- A representative étale at the distinguished source point defines an étale germ morphism. -/
theorem ofRepresentative {X Y : Germ} (r : Hom.Representative X Y)
    (hr : r.hom.EtaleAt (X.pointIn r.neighborhood r.mem_neighborhood)) :
    Etale (Hom.mk r) := sorry

end Etale

/-- A represented germ morphism is étale exactly when its representative is étale at the
distinguished source point. -/
theorem etale_mk_iff {X Y : Germ} (r : Hom.Representative X Y) :
    Etale (Hom.mk r) ↔
      r.hom.EtaleAt (X.pointIn r.neighborhood r.mem_neighborhood) := sorry

/-- Stacks 04QS: a germ morphism is étale exactly when it has a representative that is an étale
morphism of schemes on its whole neighborhood. This holds because étaleness at a point is an
open condition. -/
theorem etale_iff_exists_etale_representative {X Y : Germ} (f : X ⟶ Y) :
    Etale f ↔ ∃ r : Hom.Representative X Y, Hom.mk r = f ∧ AlgebraicGeometry.Etale r.hom :=
  sorry

/-- The identity morphism of a scheme germ is étale. -/
instance instEtaleId (X : Germ) : Etale (𝟙 X) := sorry

/-- A composite of étale morphisms of scheme germs is étale. -/
instance instEtaleComp {X Y Z : Germ} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale f] [Etale g] : Etale (f ≫ g) := sorry

end AlgebraicGeometry.Scheme.Germ
