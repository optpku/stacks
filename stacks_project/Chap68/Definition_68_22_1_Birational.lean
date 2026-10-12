/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints

/-!
# Birational morphisms of algebraic spaces

A morphism of decent algebraic spaces with finitely many irreducible components
is birational when it bijects generic points of irreducible components and
induces an isomorphism of scheme stalks at those generic points, computed on
the schematic locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The local ring map `𝒪_{Y, f(x)} ⟶ 𝒪_{X, x}` is an isomorphism when it is so
on some pair of schematic open neighbourhoods of `x` and `f(x)`. -/
def IsIsoStalkMapAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V) (u : U.left),
    IsOpenImmersion ιX ∧ IsOpenImmersion ιY ∧ ofOverMap φ ≫ ιY = ιX ≫ f ∧
      Points.map ιX (ofOver.pointsEquiv U u) = x ∧ IsIso (φ.left.stalkMap u)

/-- Unfold the schematic-neighbourhood characterization of a stalk isomorphism
at a point. -/
theorem isIsoStalkMapAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    IsIsoStalkMapAt f x ↔
      ∃ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V) (u : U.left),
        IsOpenImmersion ιX ∧ IsOpenImmersion ιY ∧ ofOverMap φ ≫ ιY = ιX ≫ f ∧
          Points.map ιX (ofOver.pointsEquiv U u) = x ∧ IsIso (φ.left.stalkMap u) :=
  sorry

namespace IsIsoStalkMapAt

/-- A commuting square of schematic open neighbourhoods whose scheme-level stalk
map is an isomorphism witnesses `IsIsoStalkMapAt`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    {U V : Over S} {ιX : ofOver U ⟶ X} {ιY : ofOver V ⟶ Y} {φ : U ⟶ V} {u : U.left}
    [IsOpenImmersion ιX] [IsOpenImmersion ιY] (hcomm : ofOverMap φ ≫ ιY = ιX ≫ f)
    (hx : Points.map ιX (ofOver.pointsEquiv U u) = x) [IsIso (φ.left.stalkMap u)] :
    IsIsoStalkMapAt f x :=
  sorry

/-- On the schematic loci of the source and target, a stalk isomorphism at `x`
is independent of the choice of schematic open neighbourhoods. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    IsIsoStalkMapAt f x ↔
      x ∈ schematicLocus X ∧ Points.map f x ∈ schematicLocus Y ∧
        ∀ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V) (u : U.left),
          IsOpenImmersion ιX → IsOpenImmersion ιY → ofOverMap φ ≫ ιY = ιX ≫ f →
            Points.map ιX (ofOver.pointsEquiv U u) = x → IsIso (φ.left.stalkMap u) :=
  sorry

end IsIsoStalkMapAt

/-- A morphism of decent algebraic spaces with finitely many irreducible
components is birational if it bijects generic points of irreducible components
and induces an isomorphism of local rings at every source generic point. -/
@[mk_iff]
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
