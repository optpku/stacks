/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints

/-!
# Birational Morphisms at Generic Points

This module defines birational scheme morphisms through their action on the
generic points of irreducible components and on the corresponding local rings.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

/-- A scheme morphism is birational when it bijects the generic points of
irreducible components and induces an isomorphism on the stalk at every generic
point of the source. -/
class IsBirational {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- The underlying map bijects the generic points of irreducible components. -/
  bijOn_genericPoints : Set.BijOn f.base (genericPoints X) (genericPoints Y)
  /-- The stalk map at every source generic point is an isomorphism. -/
  isIso_stalkMap {η : X} : η ∈ genericPoints X → IsIso (f.stalkMap η)

namespace IsBirational

/-- The map on bundled generic points induced by a birational morphism. -/
def mapGenericPoint {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsBirational f)
    (η : genericPoints X) : genericPoints Y :=
  ⟨f η.1, hf.bijOn_genericPoints.mapsTo η.2⟩

/-- The underlying point of the induced map on generic points is obtained by
applying the original morphism. -/
@[simp]
theorem coe_mapGenericPoint {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsBirational f)
    (η : genericPoints X) :
    (hf.mapGenericPoint η : Y) = f η.1 := sorry

/-- The stalk map of a birational morphism at a bundled generic point is an
isomorphism. -/
instance instIsIsoStalkMapAtGenericPoint {X Y : Scheme.{u}} {f : X ⟶ Y}
    [hf : IsBirational f] (η : genericPoints X) : IsIso (f.stalkMap η.1) :=
  hf.isIso_stalkMap η.2

end IsBirational

/-- The identity morphism of a scheme is birational. -/
instance instIsBirationalIdentity (X : Scheme.{u}) : IsBirational (𝟙 X) := sorry

/-- The composite of birational scheme morphisms is birational. -/
instance instIsBirationalComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsBirational f] [IsBirational g] : IsBirational (f ≫ g) := sorry

/-- A scheme morphism is birational exactly when it bijects generic points and
induces an isomorphism on the stalk at every source generic point. -/
theorem isBirational_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsBirational f ↔
      Set.BijOn f.base (genericPoints X) (genericPoints Y) ∧
        ∀ {η : X}, η ∈ genericPoints X → IsIso (f.stalkMap η) := sorry

/-- For schemes with finitely many irreducible components, a morphism is
birational exactly when it bijects their generic points and induces an
isomorphism on the stalk at every source generic point. -/
theorem isBirational_iff_of_finiteIrreducibleComponents
    {X Y : Scheme.{u}} [Finite (irreducibleComponents X)]
    [Finite (irreducibleComponents Y)] (f : X ⟶ Y) :
    IsBirational f ↔
      Set.BijOn f.base X⁰ Y⁰ ∧
        ∀ {η : X}, η ∈ X⁰ → IsIso (f.stalkMap η) := sorry

end

end AlgebraicGeometry
