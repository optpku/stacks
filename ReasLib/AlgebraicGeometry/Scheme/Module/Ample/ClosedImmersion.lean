module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Pullback of ample modules along closed immersions

This file records preservation of ampleness for invertible scheme modules under
pullback along closed immersions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace IsAmple

/-- Pullback of an ample invertible module along a closed immersion is ample. -/
theorem pullback_of_isClosedImmersion
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    {L : X.Modules} [Invertible L] (hA : IsAmple L) :
    IsAmple ((Scheme.Modules.pullback i).obj L) := sorry

/-- An invertible module on a Noetherian scheme is ample if its pullback along a
closed immersion from another Noetherian scheme inducing a homeomorphism is ample. -/
theorem of_pullback_of_isClosedImmersion_isHomeomorph_of_isNoetherian
    {X Z : Scheme.{u}} (i : Z ⟶ X) (hi : IsHomeomorph i)
    (L : X.Modules) [IsNoetherian X] [IsNoetherian Z]
    [IsClosedImmersion i] [Invertible L]
    (hA : IsAmple ((Scheme.Modules.pullback i).obj L)) : IsAmple L := sorry

/-- An invertible module is ample if its pullback along a closed immersion
inducing a homeomorphism is ample. -/
theorem of_pullback_of_isClosedImmersion_isHomeomorph
    {X Z : Scheme.{u}} (i : Z ⟶ X) (hi : IsHomeomorph i)
    (L : X.Modules) [IsClosedImmersion i] [Invertible L]
    (hA : IsAmple ((Scheme.Modules.pullback i).obj L)) : IsAmple L := sorry

end IsAmple

/-- Pullback along a closed immersion inducing a homeomorphism preserves and
reflects ampleness of invertible modules. -/
theorem isAmple_pullback_iff_of_isClosedImmersion_isHomeomorph
    {X Z : Scheme.{u}} (i : Z ⟶ X) (hi : IsHomeomorph i)
    (L : X.Modules) [IsClosedImmersion i] [Invertible L] :
    IsAmple ((Scheme.Modules.pullback i).obj L) ↔ IsAmple L :=
  ⟨fun hA ↦ IsAmple.of_pullback_of_isClosedImmersion_isHomeomorph i hi L hA,
    fun hA ↦ hA.pullback_of_isClosedImmersion⟩

/-- Pullback along a closed immersion inducing a homeomorphism preserves and
reflects ampleness of invertible modules on Noetherian schemes. -/
theorem isAmple_pullback_iff_of_isClosedImmersion_isHomeomorph_of_isNoetherian
    {X Z : Scheme.{u}} (i : Z ⟶ X) (hi : IsHomeomorph i)
    (L : X.Modules) [IsNoetherian X] [IsNoetherian Z]
    [IsClosedImmersion i] [Invertible L] :
    IsAmple ((Scheme.Modules.pullback i).obj L) ↔ IsAmple L :=
  ⟨fun hA ↦
      IsAmple.of_pullback_of_isClosedImmersion_isHomeomorph_of_isNoetherian i hi L hA,
    fun hA ↦ hA.pullback_of_isClosedImmersion⟩

/-- Pullback along a closed immersion canonically preserves ampleness. -/
instance instIsAmple_pullback_of_isClosedImmersion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules) [Invertible L] [hA : IsAmple L] :
    IsAmple ((Scheme.Modules.pullback i).obj L) :=
  hA.pullback_of_isClosedImmersion

end AlgebraicGeometry.Scheme.Modules
