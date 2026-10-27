/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallInvariant

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.IsInvariantHom :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y), Prop)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isInvariantHom_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y),
    G.IsInvariantHom φ ↔ G.t.left ≫ φ = G.s.left ≫ φ)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isInvariantHom_iff_toPreRelation :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : Over B} (ψ : G.U ⟶ X),
    G.IsInvariantHom ψ.left ↔ G.toPreRelation.IsInvariantHom ψ)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.atlasComp :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids), G.U.left ⟶ Y)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.atlasComp_eq :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids),
    G.atlasComp f = AlgebraicSpace.toGroupoids.eval (SmallQuotient.atlas G ≫ f))

end AlgebraicGeometry.GroupoidAlgebraicSpace
