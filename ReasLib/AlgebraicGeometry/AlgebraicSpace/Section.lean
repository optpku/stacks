/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Sections of morphisms of algebraic spaces

A section of a morphism of algebraic spaces is representable, locally of finite type,
locally quasi-finite, separated, and a monomorphism. Separation properties of the
morphism imply immersion and quasi-compactness properties of its section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A section of a morphism of algebraic spaces is representable. -/
theorem relativelyRepresentable_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) :
    yoneda.relativelyRepresentable s :=
  sorry

/-- A section of a morphism of algebraic spaces is representably locally of finite type. -/
theorem locallyOfFiniteType_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf s :=
  sorry

/-- A section of a morphism of algebraic spaces is representably locally of finite type
and locally quasi-finite. -/
theorem locallyQuasiFinite_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf s :=
  sorry

/-- A section of a morphism of algebraic spaces is representably separated. -/
theorem isSeparated_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf s :=
  sorry

/-- A section of a morphism of algebraic spaces is a representable monomorphism. -/
theorem monomorphisms_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf s :=
  sorry

/-- A section of a locally separated morphism of algebraic spaces is an immersion. -/
theorem isImmersion_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) [LocallySeparated f] :
    IsImmersion s :=
  sorry

/-- A section of a separated morphism of algebraic spaces is a closed immersion. -/
theorem isClosedImmersion_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) [Separated f] :
    IsClosedImmersion s :=
  sorry

/-- A section of a quasi-separated morphism of algebraic spaces is representably
quasi-compact. -/
theorem quasiCompact_section {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f = 𝟙 T) [QuasiSeparated f] :
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
