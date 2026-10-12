/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Ramification
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.IdealSheafData
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

set_option synthInstance.checkSynthOrder false in
/-- A locally quasi-finite morphism between schemes smooth of the same relative dimension
over a Noetherian base is flat. -/
theorem flat_of_smoothSameRelativeDimension
    {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left] : Flat f.left := sorry

/-- The Kähler different of a locally quasi-finite morphism between schemes smooth of the
same relative dimension over a Noetherian base is the zero ideal sheaf of its top differential
section. -/
theorem kaehlerDifferent_eq_zeroIdealSheaf
    {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left] :
    f.left.kaehlerDifferent =
      Scheme.zeroIdealSheaf (Ramification.line f n) (Ramification.«section» f n) := sorry

set_option synthInstance.checkSynthOrder false in
/-- The closed subscheme cut out by the Kähler different of a locally quasi-finite morphism
between schemes smooth of the same relative dimension over a Noetherian base is locally
principal. -/
theorem different_isLocallyPrincipal
    {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left] :
    IsLocallyPrincipalClosedSubscheme (subschemeι (kaehlerDifferent f.left)) := sorry

/-- The Kähler different of a locally quasi-finite morphism between schemes smooth of the
same relative dimension over a Noetherian base is an effective Cartier divisor if the morphism
is étale at every associated point of its source. -/
theorem different_isEffectiveCartier
    {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left]
    (h_assoc : ∀ y : Y.left, y ∈ Y.left.associatedPoints → f.left.EtaleAt y) :
    IsEffectiveCartierDivisor (subschemeι (kaehlerDifferent f.left)) := sorry

/-- For a locally quasi-finite morphism between schemes smooth of the same relative dimension
over a Noetherian base, étaleness at the associated points of the source identifies its top
differentials with the pulled-back top differentials tensored with the sheaf of its different. -/
theorem topDifferentialsTensorDifferentIso
    {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
    [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left]
    (h_assoc : ∀ y : Y.left, y ∈ Y.left.associatedPoints → f.left.EtaleAt y) :
    Nonempty
      ((Λ[n] ((RingedSpace.Hom.pullback f.left.toShHom).obj Ω[X.hom.toShHom])) ⊗
          (@Scheme.IdealSheafData.associatedSheaf Y.left f.left.kaehlerDifferent
            (different_isEffectiveCartier n f h_assoc)) ≅
        Λ[n] Ω[Y.hom.toShHom]) := sorry

end AlgebraicGeometry.Scheme.Hom
