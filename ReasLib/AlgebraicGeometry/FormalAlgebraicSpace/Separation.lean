/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Separation conditions for morphisms of presheaves over a scheme

For morphisms of presheaves on the over-category of a scheme, separatedness and
quasi-separatedness record representable properties of the relative pullback
diagonal. These predicates apply in particular to morphisms of formal algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of presheaves over a scheme is separated when its relative pullback
diagonal is a representable closed immersion. -/
@[mk_iff]
class Separated {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop where
  /-- The relative pullback diagonal is a representable closed immersion. -/
  isClosedImmersion_diagonal :
    (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal f)

/-- A morphism of presheaves over a scheme is quasi-separated when its relative pullback
diagonal is a representable quasi-compact morphism. -/
@[mk_iff]
class QuasiSeparated {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop where
  /-- The relative pullback diagonal is a representable quasi-compact morphism. -/
  quasiCompact_diagonal :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal f)

namespace Separated

/-- The identity morphism of presheaves over a scheme is separated. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : Separated (𝟙 X) := sorry

/-- An isomorphism of presheaves over a scheme is separated. -/
instance of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) [IsIso f] :
    Separated f := sorry

/-- A morphism of presheaves over a scheme is separated if and only if its relative
pullback diagonal is a representable closed immersion. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Separated f ↔
      (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf
        (pullback.diagonal f) := sorry

end Separated

namespace QuasiSeparated

/-- The identity morphism of presheaves over a scheme is quasi-separated. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : QuasiSeparated (𝟙 X) := sorry

/-- An isomorphism of presheaves over a scheme is quasi-separated. -/
instance of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) [IsIso f] :
    QuasiSeparated f := sorry

/-- A separated morphism of presheaves over a scheme is quasi-separated. -/
instance (priority := 900) of_separated {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [Separated f] : QuasiSeparated f := sorry

/-- A morphism of presheaves over a scheme is quasi-separated if and only if its relative
pullback diagonal is a representable quasi-compact morphism. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    QuasiSeparated f ↔
      (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf
        (pullback.diagonal f) := sorry

end QuasiSeparated

end AlgebraicGeometry.FormalAlgebraicSpace
