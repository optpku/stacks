/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Representable

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism of presheaves on schemes over `S` has the representable morphism
property induced by `P` if it is representable and every represented pullback
over a target section has underlying scheme morphism satisfying `P`. -/
abbrev representableMorphismProperty (S : Scheme.{u}) (P : MorphismProperty Scheme.{u}) :
    MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.over P).presheaf

/-- For a base-change-stable, fppf-local scheme morphism property, a Yoneda
transformation between schemes over a base has the induced representable property
if and only if its underlying scheme morphism has the original property. -/
lemma representableMorphismProperty_yoneda_map_iff {S : Scheme.{u}} {X Y : Over S}
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage] (f : X ⟶ Y) :
    representableMorphismProperty S P (yoneda.map f) ↔ P f.left := sorry

/-- If two scheme-morphism properties satisfy the standing stability and fppf-locality
conditions and the first implies the second, the induced representable morphism
properties over any scheme are ordered in the same way. -/
lemma representableMorphismProperty_mono {S : Scheme.{u}}
    {P Q : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    [Q.IsStableUnderBaseChange] [Q.IsLocalAtTarget Scheme.fppfPrecoverage]
    (h : P ≤ Q) :
    representableMorphismProperty S P ≤ representableMorphismProperty S Q := sorry

namespace representableMorphismProperty

/-- A composite of representable morphisms satisfying a composition-stable scheme
morphism property again satisfies that property. -/
lemma comp_mem {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    [P.IsStableUnderComposition]
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : representableMorphismProperty S P a)
    (hb : representableMorphismProperty S P b) :
    representableMorphismProperty S P (a ≫ b) := sorry

/-- The binary product of two representable morphisms satisfying a base-change-stable,
fppf-local, composition-stable scheme morphism property again satisfies that property. -/
lemma prod_map {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    [P.IsStableUnderComposition]
    {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u}
    (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (ha₁ : representableMorphismProperty S P a₁)
    (ha₂ : representableMorphismProperty S P a₂) :
    representableMorphismProperty S P (Limits.prod.map a₁ a₂) := sorry

end representableMorphismProperty

end AlgebraicGeometry.Scheme
