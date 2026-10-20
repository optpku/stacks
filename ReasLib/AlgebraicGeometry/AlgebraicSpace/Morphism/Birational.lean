/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of decent algebraic spaces with finitely many irreducible
components is birational if it bijects generic points of irreducible components
and induces an isomorphism of local rings at every source generic point. -/
@[mk_iff, stacks 0ACV]
class IsBirational {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) : Prop where
  /-- `|f|` bijects generic points of irreducible components. -/
  bijOn_genericPoints : Set.BijOn (Points.map f) (genericPoints X) (genericPoints Y)
  /-- The schematic-locus local ring map is an isomorphism at every generic
  point of `|X|`. -/
  isIso_stalkMap {x : Points X} : x ∈ genericPoints X → IsIsoStalkMapAt f x

namespace IsBirational

/-- A birational morphism bijects generic points of irreducible components. -/
theorem bijOn {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} [IsBirational f] :
    Set.BijOn (Points.map f) (genericPoints X) (genericPoints Y) :=
  sorry

/-- A birational morphism induces an isomorphism of schematic-locus local rings
at every generic point of the source. -/
theorem isIsoStalkMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} [IsBirational f] {x : Points X} (hx : x ∈ genericPoints X) :
    IsIsoStalkMapAt f x :=
  sorry

/-- The two defining conditions of `IsBirational` may be supplied together. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} (h_bij : Set.BijOn (Points.map f) (genericPoints X) (genericPoints Y))
    (h_stalk : ∀ {x : Points X}, x ∈ genericPoints X → IsIsoStalkMapAt f x) :
    IsBirational f :=
  sorry

end IsBirational

/-- The identity morphism of a decent algebraic space with finitely many
irreducible components is birational. -/
instance instIsBirational_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [HasFiniteIrreducibleComponents X] :
    IsBirational (𝟙 X) :=
  sorry

/-- The composite of birational morphisms of decent algebraic spaces with
finitely many irreducible components is birational. -/
instance instIsBirational_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    [HasFiniteIrreducibleComponents Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsBirational f] [IsBirational g] :
    IsBirational (f ≫ g) :=
  sorry

/-- A morphism of schemes over `S` is birational if and only if the induced
morphism of algebraic spaces is birational. -/
theorem isBirational_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    [Finite (irreducibleComponents U.left)] [Finite (irreducibleComponents V.left)]
    (f : U ⟶ V) :
    IsBirational (ofOverMap f) ↔ AlgebraicGeometry.IsBirational f.left :=
  sorry

/-- A birational morphism of schemes over `S` induces a birational morphism of
the associated algebraic spaces. -/
instance instIsBirational_ofOverMap {S : Scheme.{u}} {U V : Over S}
    [Finite (irreducibleComponents U.left)] [Finite (irreducibleComponents V.left)]
    (f : U ⟶ V) [AlgebraicGeometry.IsBirational f.left] :
    IsBirational (ofOverMap f) :=
  sorry

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components restricts to a birational morphism of schemes on dense
representable open subspaces. -/
theorem exists_dense_representable_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} [IsBirational f] :
    ∃ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V),
      IsOpenImmersion ιX ∧ IsOpenImmersion ιY ∧
        (∀ (τX : TopologicalSpace (Points X)),
          IsPointsTopology X τX → @Dense (Points X) τX (Set.range (Points.map ιX))) ∧
        (∀ (τY : TopologicalSpace (Points Y)),
          IsPointsTopology Y τY → @Dense (Points Y) τY (Set.range (Points.map ιY))) ∧
        ofOverMap φ ≫ ιY = ιX ≫ f ∧ AlgebraicGeometry.IsBirational φ.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
