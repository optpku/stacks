/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Varieties and dominant rational maps

This file packages varieties over a fixed field into a category whose
morphisms are dominant rational maps over that field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Varieties over `k`, as a subtype of schemes over `Spec k`. -/
def VarietyDominantRationalMapCat (k : Type u) [Field k] :=
  { X : SchemeOverField k // Variety X }

namespace VarietyDominantRationalMapCat

variable {k : Type u} [Field k]

/-- The scheme over `k` underlying an object of `VarietyDominantRationalMapCat k`. -/
def obj (X : VarietyDominantRationalMapCat k) : SchemeOverField k :=
  X.1

/-- The underlying scheme over `k` of every object is a variety. -/
instance instVarietyObj (X : VarietyDominantRationalMapCat k) : Variety X.obj :=
  X.2

/-- A morphism is a dominant rational map commuting with the maps to `Spec k`. -/
def Hom (X Y : VarietyDominantRationalMapCat k) :=
  { f : X.obj.left ⤏ Y.obj.left //
      f.IsOver (Spec (CommRingCat.of k)) ∧ f.IsDominant }

namespace Hom

/-- The identity dominant rational map of a variety over `k`. -/
def id (X : VarietyDominantRationalMapCat k) : Hom X X :=
  ⟨Scheme.RationalMap.id X.obj.left, inferInstance, inferInstance⟩

/-- Composition of dominant rational maps over `k`. -/
noncomputable def comp {X Y Z : VarietyDominantRationalMapCat k}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z := by
  -- Local instance justification (proof-local temporary data): `f` stores the required dominance proof.
  letI : f.1.IsDominant := f.2.2
  -- Local instance justification (proof-local temporary data): `g` stores the required dominance proof.
  letI : g.1.IsDominant := g.2.2
  -- Local instance justification (proof-local temporary data): `f` stores the required base-compatibility proof.
  letI : f.1.IsOver (Spec (CommRingCat.of k)) := f.2.1
  -- Local instance justification (proof-local temporary data): `g` stores the required base-compatibility proof.
  letI : g.1.IsOver (Spec (CommRingCat.of k)) := g.2.1
  exact ⟨f.1.comp g.1, inferInstance, inferInstance⟩

/-- Identity on the source is a left identity for dominant rational-map composition. -/
theorem id_comp {X Y : VarietyDominantRationalMapCat k} (f : Hom X Y) :
    comp (id X) f = f := sorry

/-- Identity on the target is a right identity for dominant rational-map composition. -/
theorem comp_id {X Y : VarietyDominantRationalMapCat k} (f : Hom X Y) :
    comp f (id Y) = f := sorry

/-- Composition of dominant rational maps over `k` is associative. -/
theorem comp_assoc {W X Y Z : VarietyDominantRationalMapCat k}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- The category of varieties over `k` and dominant rational maps over `Spec k`. -/
noncomputable instance instCategory : Category (VarietyDominantRationalMapCat k) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end VarietyDominantRationalMapCat

end AlgebraicGeometry
