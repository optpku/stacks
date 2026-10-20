/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Geometrically reduced, connected, irreducible, and integral algebraic spaces

An algebraic space over a field `k` is geometrically reduced, connected, irreducible,
or integral when every field base change along `Spec K ⟶ Spec k` has the corresponding
property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

/-- An algebraic space over a field `k` is geometrically reduced if every base change
along a field extension `K/k` is reduced. -/
@[mk_iff]
class GeometricallyReduced (X : AlgebraicSpace (Spec (of k))) : Prop where
  /-- Every field base change of `X` is reduced. -/
  isReduced_baseChange :
    ∀ (K : Type u) [Field K] [Algebra k K],
      IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X)

namespace GeometricallyReduced

/-- A geometrically reduced algebraic space remains reduced after every field base change. -/
theorem spec (X : AlgebraicSpace (Spec (of k))) [GeometricallyReduced X]
    (K : Type u) [Field K] [Algebra k K] :
    IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X) :=
  sorry

/-- Geometric reducedness is equivalent to reducedness after every field base change. -/
theorem iff (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyReduced X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X) :=
  sorry

end GeometricallyReduced

/-- An algebraic space over a field `k` is geometrically connected if every base change
along a field extension `K/k` has connected space of points. -/
@[mk_iff]
class GeometricallyConnected (X : AlgebraicSpace (Spec (of k))) : Prop where
  /-- Every field base change of `X` has connected space of points. -/
  connectedSpace_baseChange :
    ∀ (K : Type u) [Field K] [Algebra k K],
      ConnectedSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X))

namespace GeometricallyConnected

/-- A geometrically connected algebraic space remains connected after every field base change. -/
theorem spec (X : AlgebraicSpace (Spec (of k))) [GeometricallyConnected X]
    (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)) :=
  sorry

/-- Geometric connectedness is equivalent to connectedness of points after every field
base change. -/
theorem iff (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyConnected X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)) :=
  sorry

end GeometricallyConnected

/-- An algebraic space over a field `k` is geometrically irreducible if every base change
along a field extension `K/k` has irreducible space of points. -/
@[mk_iff]
class GeometricallyIrreducible (X : AlgebraicSpace (Spec (of k))) : Prop where
  /-- Every field base change of `X` has irreducible space of points. -/
  irreducibleSpace_baseChange :
    ∀ (K : Type u) [Field K] [Algebra k K],
      IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X))

namespace GeometricallyIrreducible

/-- A geometrically irreducible algebraic space remains irreducible after every field
base change. -/
theorem spec (X : AlgebraicSpace (Spec (of k))) [GeometricallyIrreducible X]
    (K : Type u) [Field K] [Algebra k K] :
    IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)) :=
  sorry

/-- Geometric irreducibility is equivalent to irreducibility of points after every field
base change. -/
theorem iff (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyIrreducible X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)) :=
  sorry

end GeometricallyIrreducible

/-- An algebraic space over a field `k` is geometrically integral if every base change
along a field extension `K/k` is decent, reduced, and has irreducible space of points. -/
@[mk_iff]
class GeometricallyIntegral (X : AlgebraicSpace (Spec (of k))) : Prop where
  /-- Every field base change of `X` is decent. -/
  isDecent_baseChange :
    ∀ (K : Type u) [Field K] [Algebra k K],
      IsDecent (baseChange (Spec.map (ofHom (algebraMap k K))) X)
  /-- Every field base change of `X` is reduced. -/
  isReduced_baseChange :
    ∀ (K : Type u) [Field K] [Algebra k K],
      IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X)
  /-- Every field base change of `X` has irreducible space of points. -/
  irreducibleSpace_baseChange :
    ∀ (K : Type u) [Field K] [Algebra k K],
      IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X))

namespace GeometricallyIntegral

/-- A geometrically integral algebraic space remains decent, reduced, and irreducible after
every field base change. -/
theorem spec (X : AlgebraicSpace (Spec (of k))) [GeometricallyIntegral X]
    (K : Type u) [Field K] [Algebra k K] :
    IsDecent (baseChange (Spec.map (ofHom (algebraMap k K))) X) ∧
      IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X) ∧
      IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)) :=
  sorry

/-- Geometric integrality is equivalent to decency, reducedness, and irreducibility of points
after every field base change. -/
theorem iff (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyIntegral X ↔
      (∀ (K : Type u) [Field K] [Algebra k K],
          IsDecent (baseChange (Spec.map (ofHom (algebraMap k K))) X)) ∧
        (∀ (K : Type u) [Field K] [Algebra k K],
          IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X)) ∧
        ∀ (K : Type u) [Field K] [Algebra k K],
          IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)) :=
  sorry

end GeometricallyIntegral

/-- The algebraic space `Spec k` over itself is geometrically reduced. -/
instance instGeometricallyReduced_ofOver_id :
    GeometricallyReduced (ofOver (Over.mk (𝟙 (Spec (of k))))) :=
  sorry

/-- The algebraic space `Spec k` over itself is geometrically connected. -/
instance instGeometricallyConnected_ofOver_id :
    GeometricallyConnected (ofOver (Over.mk (𝟙 (Spec (of k))))) :=
  sorry

/-- The algebraic space `Spec k` over itself is geometrically irreducible. -/
instance instGeometricallyIrreducible_ofOver_id :
    GeometricallyIrreducible (ofOver (Over.mk (𝟙 (Spec (of k))))) :=
  sorry

/-- The algebraic space `Spec k` over itself is geometrically integral. -/
instance instGeometricallyIntegral_ofOver_id :
    GeometricallyIntegral (ofOver (Over.mk (𝟙 (Spec (of k))))) :=
  sorry

variable {X : AlgebraicSpace (Spec (of k))}

/-- A geometrically integral algebraic space over a field is geometrically reduced. -/
instance (priority := low) instGeometricallyReduced_of_geometricallyIntegral
    [GeometricallyIntegral X] : GeometricallyReduced X :=
  sorry

/-- A geometrically integral algebraic space over a field is geometrically irreducible. -/
instance (priority := low) instGeometricallyIrreducible_of_geometricallyIntegral
    [GeometricallyIntegral X] : GeometricallyIrreducible X :=
  sorry

/-- A geometrically irreducible algebraic space over a field is geometrically connected. -/
instance (priority := low) instGeometricallyConnected_of_geometricallyIrreducible
    [GeometricallyIrreducible X] : GeometricallyConnected X :=
  sorry

namespace GeometricallyIntegral

/-- A decent geometrically reduced and geometrically irreducible algebraic space is
geometrically integral. -/
instance of_geometricallyReduced_of_geometricallyIrreducible
    [IsDecent X] [GeometricallyReduced X] [GeometricallyIrreducible X] :
    GeometricallyIntegral X :=
  sorry

/-- For a decent algebraic space over a field, geometric integrality is equivalent
to geometric reducedness together with geometric irreducibility. -/
theorem iff_geometricallyReduced_and_geometricallyIrreducible [IsDecent X] :
    GeometricallyIntegral X ↔ GeometricallyReduced X ∧ GeometricallyIrreducible X :=
  sorry

end GeometricallyIntegral

end AlgebraicGeometry.AlgebraicSpace
