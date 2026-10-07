module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme

/-!
# Universal property of zero schemes on algebraic spaces

A morphism of algebraic spaces over `S` pulls a section of an invertible module
back to zero if and only if it factors through the zero scheme of that section.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical section of an invertible module vanishes after pullback along
the closed immersion of its zero scheme. -/
theorem zeroSchemeι_pullbackSections_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    Modules.sectionsPullback (zeroSchemeι L s) L s = 0 :=
  sorry

/-- Every closed immersion on which a section vanishes factors through the zero
scheme of that section. -/
theorem exists_factorization_zeroScheme_of_pullbackSections_eq_zero
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) (i : Z ⟶ X) [IsClosedImmersion i]
    (hzero : Modules.sectionsPullback i L s = 0) :
    ∃ g : Z ⟶ (zeroScheme L s).X, g ≫ zeroSchemeι L s = i :=
  sorry

/-- Pullback of a section vanishes if and only if the morphism factors through the
zero scheme of that section. -/
theorem pullbackSections_eq_zero_iff_exists_factorization_zeroScheme
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) (f : Y ⟶ X) :
    Modules.sectionsPullback f L s = 0 ↔
      ∃ g : Y ⟶ (zeroScheme L s).X, g ≫ zeroSchemeι L s = f :=
  sorry

/-- Pullback of a section vanishes if and only if the zero ideal vanishes along
the morphism. -/
theorem pullbackSections_eq_zero_iff_vanishes {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (f : Y ⟶ X) :
    Modules.sectionsPullback f L s = 0 ↔ vanishes f (zeroIdealSubobject L s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
