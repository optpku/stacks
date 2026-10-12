/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Remark_63_3_14_Comparison

/-!
# Coherence of underived étale lower shriek

Remark 63.3.14: associativity of the composition identifications of `f_!`,
and compatibility of those identifications with cartesian base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Remark 63.3.14 (1): for composable separated locally finite-type scheme
morphisms `f`, `g`, and `h`, the identifications
`(f ≫ g ≫ h)_! ≅ (f ≫ g)_! ⋙ h_! ≅ f_! ⋙ g_! ⋙ h_!` and
`(f ≫ g ≫ h)_! ≅ f_! ⋙ (g ≫ h)_! ≅ f_! ⋙ g_! ⋙ h_!` form a commutative
square of natural transformations. -/
@[stacks 0F77]
theorem etaleLowerShriekCompIso_assoc
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    [IsSeparated h] [LocallyOfFiniteType h] :
    etaleLowerShriekCompIso_assoc_left f g h =
      eqToHom (etaleLowerShriek_assoc f g h) ≫
        etaleLowerShriekCompIso_assoc_right f g h :=
  sorry

/-- Remark 63.3.14 (2): for two vertically pasted cartesian squares of schemes
with vertical maps separated and locally of finite type, composition of
`etaleLowerShriek` is compatible with the base-change identifications of
Lemma 63.3.12. -/
@[stacks 0F77]
theorem etaleLowerShriekCompIso_baseChange_vcomp
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
    (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [IsSeparated g'] [LocallyOfFiniteType g'] :
    etaleLowerShriekCompIso_baseChange_vcomp_outer f g f' g' a b c h_upper h_lower =
      etaleLowerShriekCompIso_baseChange_vcomp_inner f g f' g' a b c h_upper h_lower :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
