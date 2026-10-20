/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponent
public import ReasLib.Topology.ConnectedComponents.Set

/-!
# Geometric connectedness of canonical connected components

This leaf records the componentwise consequence of geometric irreducibility for a scheme with
finitely many irreducible components.  It is stated for a direct structure morphism so it can be
used without rebuilding an `Over` wrapper.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace GeometricallyConnected.Components

/-- A connected component has a unique flat ideal-sheaf presentation, and every such
presentation is geometrically connected over the base field. -/
@[stacks 054S]
def isConnected
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (C : _root_.ConnectedComponents X) : Prop :=
  (∃! I : X.IdealSheafData,
      Flat I.subschemeι ∧ (I.support : Set X) = C.set) ∧
    ∀ I : X.IdealSheafData,
      Flat I.subschemeι ∧ (I.support : Set X) = C.set →
        GeometricallyConnected (I.subschemeι ≫ f)

/-- Geometric connectedness of a component is equivalent to unique existence of its flat
ideal-sheaf presentation together with geometric connectedness of every such presentation. -/
theorem isConnected_iff
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (C : _root_.ConnectedComponents X) :
    isConnected f C ↔
      (∃! I : X.IdealSheafData,
          Flat I.subschemeι ∧ (I.support : Set X) = C.set) ∧
        ∀ I : X.IdealSheafData,
          Flat I.subschemeι ∧ (I.support : Set X) = C.set →
            GeometricallyConnected (I.subschemeι ≫ f) := sorry

/-- If a scheme has finitely many irreducible components and all canonical reduced components are
geometrically irreducible, then every connected component is geometrically connected. -/
@[stacks 054S]
theorem of_geometricallyIrreducible
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [Finite (irreducibleComponents X)]
    (hgeom : GeometricallyIrreducible.Components.all f)
    (C : _root_.ConnectedComponents X) :
    isConnected f C := sorry

end GeometricallyConnected.Components

end AlgebraicGeometry
