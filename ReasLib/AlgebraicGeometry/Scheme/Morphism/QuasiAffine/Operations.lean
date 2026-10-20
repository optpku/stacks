module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Operations on Quasi-Affine Scheme Morphisms

This leaf contains standard construction, composition, base-change, and
relative-over-a-base APIs for quasi-affine morphisms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The composite of quasi-affine morphisms is quasi-affine. -/
theorem QuasiAffineHom.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : QuasiAffineHom f) (hg : QuasiAffineHom g) :
    QuasiAffineHom (f ≫ g) := sorry

/-- Quasi-affineness is preserved by arbitrary base change. -/
theorem QuasiAffineHom.baseChange
    {X S S' : Scheme.{u}} {f : X ⟶ S} (g : S' ⟶ S)
    (hf : QuasiAffineHom f) :
    QuasiAffineHom (pullback.snd f g) := sorry

/-- A quasi-compact immersion is quasi-affine. -/
theorem IsImmersion.quasiAffineHom_of_quasiCompact
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsImmersion f) (hqc : QuasiCompact f) :
    QuasiAffineHom f := sorry

/-- From an affine source, quasi-affineness is equivalent to quasi-compactness. -/
theorem quasiAffineHom_iff_quasiCompact_of_isAffine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] :
    QuasiAffineHom f ↔ QuasiCompact f := sorry

/-- A morphism from an affine scheme to a quasi-separated scheme is quasi-affine. -/
theorem quasiAffineHom_of_isAffine_of_quasiSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [QuasiSeparatedSpace S] :
    QuasiAffineHom f := sorry

/-- A morphism over a base from a quasi-affine morphism to a quasi-separated
morphism is quasi-affine. -/
theorem QuasiAffineHom.of_over_quasiSeparated
    {X Y S : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S} {g : X ⟶ Y}
    (w : g ≫ y = x) (hx : QuasiAffineHom x) (hy : QuasiSeparated y) :
    QuasiAffineHom g := sorry

/-- A morphism from a quasi-affine scheme to a quasi-separated scheme is quasi-affine. -/
theorem Scheme.IsQuasiAffine.quasiAffineHom_of_quasiSeparated
    {X Y : Scheme.{u}} (g : X ⟶ Y) (hX : X.IsQuasiAffine) [QuasiSeparatedSpace Y] :
    QuasiAffineHom g := sorry

end AlgebraicGeometry
