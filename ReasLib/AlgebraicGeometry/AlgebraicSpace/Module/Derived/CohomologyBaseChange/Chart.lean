/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation

/-!
# Étale scheme charts of a cartesian square of algebraic spaces

A chart of a morphism square of algebraic spaces over `S` consists of étale scheme
objects `U → X`, `V → Y`, and `V' → Y'` together with morphisms of schemes over `S`
making the two squares commute. The remaining vertex is the chosen scheme fibre
product `U' = V' ×_V U`, and cartesianness of the ambient square induces `U' → X'`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- An étale scheme chart of a square of algebraic spaces over `S`, with vertices
`U` étale over `X`, `V` étale over `Y`, and `V'` étale over `Y'`. -/
structure EtaleBaseChangeChart (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) where
  /-- The étale scheme object `U` of the small étale site of `X`. -/
  U : smallEtaleSite X
  /-- The étale scheme object `V` of the small étale site of `Y`. -/
  V : smallEtaleSite Y
  /-- The étale scheme object `V'` of the small étale site of `Y'`. -/
  V' : smallEtaleSite Y'
  /-- The morphism of schemes over `S` from `U` to `V`. -/
  mapU : U.left ⟶ V.left
  /-- The morphism of schemes over `S` from `V'` to `V`. -/
  mapV' : V'.left ⟶ V.left
  /-- The square `U → X`, `V → Y`, `U → V` commutes with `f`. -/
  wU : U.hom ≫ f = ofOverMap mapU ≫ V.hom
  /-- The square `V' → Y'`, `V → Y`, `V' → V` commutes with `g`. -/
  wV' : V'.hom ≫ g = ofOverMap mapV' ≫ V.hom

namespace EtaleBaseChangeChart

variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Reconstruct an étale base-change chart from its three étale scheme objects, the two
morphisms of schemes over `S`, and the two commuting squares. -/
def of (U : smallEtaleSite X) (V : smallEtaleSite Y) (V' : smallEtaleSite Y')
    (mapU : U.left ⟶ V.left) (mapV' : V'.left ⟶ V.left)
    (wU : U.hom ≫ f = ofOverMap mapU ≫ V.hom)
    (wV' : V'.hom ≫ g = ofOverMap mapV' ≫ V.hom) :
    EtaleBaseChangeChart g' f' f g where
  U := U
  V := V
  V' := V'
  mapU := mapU
  mapV' := mapV'
  wU := wU
  wV' := wV'

/-- An étale base-change chart records commuting squares over `f` and `g`, étale structural
morphisms, and the scheme-level cospan identity of its two chart maps. -/
theorem spec (c : EtaleBaseChangeChart g' f' f g) :
    c.U.hom ≫ f = ofOverMap c.mapU ≫ c.V.hom ∧
      c.V'.hom ≫ g = ofOverMap c.mapV' ≫ c.V.hom ∧
        Etale c.U.hom ∧ Etale c.V.hom ∧ Etale c.V'.hom ∧
          c.mapU.left ≫ c.V.left.hom = c.U.left.hom ∧
            c.mapV'.left ≫ c.V.left.hom = c.V'.left.hom := sorry

/-- The chosen scheme fibre product `U' = V' ×_V U` of a chart. -/
def schemeU' (c : EtaleBaseChangeChart g' f' f g) : Scheme.{u} :=
  pullback c.mapU.left c.mapV'.left

/-- The projection `U' ⟶ U` of the chosen scheme fibre product. -/
def fst (c : EtaleBaseChangeChart g' f' f g) : c.schemeU' ⟶ c.U.left.left :=
  pullback.fst c.mapU.left c.mapV'.left

/-- The projection `U' ⟶ V'` of the chosen scheme fibre product. -/
def snd (c : EtaleBaseChangeChart g' f' f g) : c.schemeU' ⟶ c.V'.left.left :=
  pullback.snd c.mapU.left c.mapV'.left

/-- The object of `Sch/S` with underlying scheme `U'` and structure morphism through `U`. -/
def overObj (c : EtaleBaseChangeChart g' f' f g) : Over S :=
  Over.mk (c.fst ≫ c.U.left.hom)

/-- The first fibre-product projection preserves the structure morphism to S. -/
theorem fst_comp_structure (c : EtaleBaseChangeChart g' f' f g) :
    c.fst ≫ c.U.left.hom = c.overObj.hom := sorry

/-- The second fibre-product projection preserves the structure morphism to S. -/
theorem snd_comp_structure (c : EtaleBaseChangeChart g' f' f g) :
    c.snd ≫ c.V'.left.hom = c.overObj.hom := sorry

/-- The morphism `U' ⟶ U` in `Sch/S` induced by the first projection. -/
def toUOver (c : EtaleBaseChangeChart g' f' f g) : c.overObj ⟶ c.U.left :=
  Over.homMk c.fst c.fst_comp_structure

/-- The morphism `U' ⟶ V'` in `Sch/S` induced by the second projection. -/
def toV'Over (c : EtaleBaseChangeChart g' f' f g) : c.overObj ⟶ c.V'.left :=
  Over.homMk c.snd c.snd_comp_structure

/-- The two étale charts of `X` and `Y'` agree after mapping to `Y`, so they lift across a
cartesian square. -/
theorem toX'_lift_comm (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g) :
    (ofOverMap c.toUOver ≫ c.U.hom) ≫ f =
      (ofOverMap c.toV'Over ≫ c.V'.hom) ≫ g := sorry

/-- The induced morphism `U' → X'` obtained by lifting the pair of étale charts of `X` and
`Y'` along a cartesian square of algebraic spaces. -/
def toX' (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g) :
    ofOver c.overObj ⟶ X' :=
  sq.lift (ofOverMap c.toUOver ≫ c.U.hom) (ofOverMap c.toV'Over ≫ c.V'.hom)
    (c.toX'_lift_comm sq)

/-- The first projection of `toX'` recovers the composite `U' → U → X`. -/
theorem toX'_comp_g' (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g) :
    c.toX' sq ≫ g' = ofOverMap c.toUOver ≫ c.U.hom := sorry

/-- The second projection of `toX'` recovers the composite `U' → V' → Y'`. -/
theorem toX'_comp_f' (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g) :
    c.toX' sq ≫ f' = ofOverMap c.toV'Over ≫ c.V'.hom := sorry

/-- The induced chart morphism `U' → X'` is étale. -/
theorem etale_toX' (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g) :
    Etale (c.toX' sq) := sorry

/-- `schemeU'` is the chosen pullback of the underlying scheme morphisms of the chart. -/
theorem schemeU'_eq (c : EtaleBaseChangeChart g' f' f g) :
    c.schemeU' = pullback c.mapU.left c.mapV'.left := sorry

end EtaleBaseChangeChart

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
