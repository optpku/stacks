/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Properties of the diagonal of an algebraic space

The diagonal of an algebraic space is representably locally of finite type,
a monomorphism, separated, and locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The diagonal of an algebraic space over a scheme is representably locally of finite type. -/
@[stacks 02X4]
theorem locallyOfFiniteType_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (diag F) :=
  sorry

/-- The diagonal of an algebraic space over a scheme is representably a monomorphism. -/
@[stacks 02X4]
theorem monomorphisms_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf (diag F) :=
  sorry

/-- The diagonal of an algebraic space over a scheme is representably separated. -/
@[stacks 02X4]
theorem isSeparated_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (diag F) :=
  sorry

/-- The diagonal of an algebraic space over a scheme is representably locally of finite type
and locally quasi-finite. -/
@[stacks 02X4]
theorem locallyQuasiFinite_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf (diag F) :=
  sorry

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representable
by schemes. -/
@[stacks 03HK]
theorem relativelyRepresentable_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    yoneda.relativelyRepresentable (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
locally of finite type. -/
@[stacks 03HK]
theorem locallyOfFiniteType_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
a monomorphism. -/
@[stacks 03HK]
theorem monomorphisms_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
separated. -/
@[stacks 03HK]
theorem isSeparated_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
locally of finite type and locally quasi-finite. -/
@[stacks 03HK]
theorem locallyQuasiFinite_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

/-- The relative diagonal of a separated morphism of algebraic spaces is a closed immersion. -/
instance instIsClosedImmersion_pullbackDiagonal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    IsClosedImmersion (pullback.diagonal f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
