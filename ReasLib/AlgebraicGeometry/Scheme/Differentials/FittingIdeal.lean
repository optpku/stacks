/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Isomorphism

/-!
# Fitting ideal sheaves of relative differentials

The Fitting ideal sheaves of relative differentials commute with arbitrary base change for
locally finite type morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The Kähler different of a locally finite type morphism is the zeroth Fitting ideal sheaf
of its relative differentials. -/
def kaehlerDifferent {Y X : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f] :
    Y.IdealSheafData :=
  Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0

/-- The Kähler different is the zeroth Fitting ideal sheaf of relative differentials. -/
theorem kaehlerDifferent_eq_fittingIdealSheaf
    {Y X : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f] :
    kaehlerDifferent f = Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0 := sorry

/-- Pulling back a Fitting ideal sheaf of relative differentials along a cartesian base change
gives the corresponding Fitting ideal sheaf of relative differentials after base change. -/
theorem fittingIdealSheaf_differentials_pullback
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (i : ℕ) :
    (Scheme.fittingIdealSheaf (Ω[f.toShHom]) i).comap (pullback.fst f g) =
      Scheme.fittingIdealSheaf (Ω[(pullback.snd f g).toShHom]) i := sorry

/-- In a cartesian square, the zeroth Fitting ideal sheaf of relative differentials after
base change is the pullback of the original zeroth Fitting ideal sheaf. -/
theorem fittingIdealSheaf_differentials_comap_of_isPullback
    {Y Y' X X' : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f]
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (sq : IsPullback g' f' f g) :
    (Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).comap g' =
      Scheme.fittingIdealSheaf (Ω[f'.toShHom]) 0 := sorry

/-- The closed subscheme of the base-changed Kähler different maps to the pullback of the
original Kähler different via the canonical ideal-sheaf pullback comparison. -/
noncomputable def fittingIdealSheaf_differentials_baseChangeComparison
    {Y Y' X X' : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f]
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (h : (Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).comap g' =
      Scheme.fittingIdealSheaf (Ω[f'.toShHom]) 0) :
    (Scheme.fittingIdealSheaf (Ω[f'.toShHom]) 0).subscheme ⟶
      pullback g' (Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).subschemeι :=
  eqToHom (congrArg (fun J : Y'.IdealSheafData ↦ J.subscheme) h.symm) ≫
    (Scheme.IdealSheafData.comapIso (Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0) g').hom

/-- In a cartesian square, the canonical comparison of the Kähler-different closed subschemes
is an isomorphism. -/
theorem fittingIdealSheaf_differentials_baseChangeComparison_isIso_of_isPullback
    {Y Y' X X' : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f]
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (sq : IsPullback g' f' f g) :
    IsIso (fittingIdealSheaf_differentials_baseChangeComparison f g g' f'
      (fittingIdealSheaf_differentials_comap_of_isPullback f g g' f' sq)) := sorry

end AlgebraicGeometry.Scheme.Hom
