/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducible components of geometrically irreducible pullbacks

This module gives component equivalences for the projections of pullbacks
along geometrically irreducible morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace GeometricallyIrreducible

/-- The second projection of a pullback along a geometrically irreducible morphism induces an
equivalence on irreducible components. -/
@[stacks 038F]
noncomputable def pullbackSndComponentsEquiv
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] :
    irreducibleComponents ((pullback f g : Scheme.{u})) ≃ irreducibleComponents Y :=
  (pullback.snd f g).irreducibleComponentsEquiv (pullback.snd f g).isOpenMap

/-- An explicit-proof form of `pullbackSndComponentsEquiv`, for arguments whose geometric
irreducibility is available as a proposition rather than an ambient instance. -/
noncomputable def pullbackSndComponentsEquiv_of
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (h : GeometricallyIrreducible f) :
    irreducibleComponents ((pullback f g : Scheme.{u})) ≃ irreducibleComponents Y :=
  @pullbackSndComponentsEquiv k _ X Y f g h

/-- The pullback component equivalence is the canonical equivalence induced by the second
projection. -/
@[stacks 038F]
theorem pullbackSndComponentsEquiv_def
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] :
    pullbackSndComponentsEquiv f g =
      (pullback.snd f g).irreducibleComponentsEquiv (pullback.snd f g).isOpenMap := sorry

/-- The first projection of a pullback along a geometrically irreducible morphism induces an
equivalence on irreducible components. -/
noncomputable def pullbackFstComponentsEquiv
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible g] :
    irreducibleComponents ((pullback f g : Scheme.{u})) ≃ irreducibleComponents X :=
  (pullback.fst f g).irreducibleComponentsEquiv (pullback.fst f g).isOpenMap

/-- An explicit-proof form of `pullbackFstComponentsEquiv`, for arguments whose geometric
irreducibility is available as a proposition rather than an ambient instance. -/
noncomputable def pullbackFstComponentsEquiv_of
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (h : GeometricallyIrreducible g) :
    irreducibleComponents ((pullback f g : Scheme.{u})) ≃ irreducibleComponents X :=
  @pullbackFstComponentsEquiv k _ X Y f g h

/-- The first-projection pullback component equivalence is induced by the canonical first
projection. -/
theorem pullbackFstComponentsEquiv_def
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible g] :
    pullbackFstComponentsEquiv f g =
      (pullback.fst f g).irreducibleComponentsEquiv (pullback.fst f g).isOpenMap := sorry

end GeometricallyIrreducible

end AlgebraicGeometry
