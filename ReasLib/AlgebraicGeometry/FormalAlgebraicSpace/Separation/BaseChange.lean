/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

/-!
# Base change of separation conditions for morphisms of presheaves over a scheme

Separated and quasi-separated morphisms of presheaves over a scheme are stable
under arbitrary base change, in particular for morphisms of formal algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Separated

/-- In a pullback square of presheaves over a scheme, the base change of a
separated morphism is separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Separated g) : Separated g' := sorry

/-- The base-change projection `pullback.snd f g` of a separated morphism
`f : X ⟶ Y` of presheaves over a scheme is separated. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : Separated f) (g : Z ⟶ Y) [HasPullback f g] :
    Separated (pullback.snd f g) := sorry

end Separated

/-- Pullback projections of separated morphisms of presheaves over a scheme
are separated. -/
instance separated_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [Separated f] [HasPullback f g] :
    Separated (pullback.snd f g) := sorry

namespace QuasiSeparated

/-- In a pullback square of presheaves over a scheme, the base change of a
quasi-separated morphism is quasi-separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : QuasiSeparated g) :
    QuasiSeparated g' := sorry

/-- The base-change projection `pullback.snd f g` of a quasi-separated morphism
`f : X ⟶ Y` of presheaves over a scheme is quasi-separated. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : QuasiSeparated f) (g : Z ⟶ Y) [HasPullback f g] :
    QuasiSeparated (pullback.snd f g) := sorry

end QuasiSeparated

/-- Pullback projections of quasi-separated morphisms of presheaves over a
scheme are quasi-separated. -/
instance quasiSeparated_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [QuasiSeparated f] [HasPullback f g] :
    QuasiSeparated (pullback.snd f g) := sorry

/-- Separated morphisms of presheaves over a scheme are stable under arbitrary
base change. -/
instance separated_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Separated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

/-- Quasi-separated morphisms of presheaves over a scheme are stable under
arbitrary base change. -/
instance quasiSeparated_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@QuasiSeparated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
