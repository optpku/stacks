/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Ramification
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Different.Smooth
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.IdealSheafData
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 49.12.6 (1): a locally quasi-finite morphism between schemes smooth of the same
relative dimension over a Noetherian base is flat. -/
@[stacks 0BWJ] #check
  (AlgebraicGeometry.Scheme.Hom.flat_of_smoothSameRelativeDimension :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
      [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
      [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left], Flat f.left)

/- Lemma 49.12.6 (2): the Kähler different is the zero ideal sheaf of the section induced by
`Λ[n] (differentialMap f)`. -/
@[stacks 0BWJ] #check
  (AlgebraicGeometry.Scheme.Hom.kaehlerDifferent_eq_zeroIdealSheaf :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
      [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
      [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left],
      f.left.kaehlerDifferent =
        Scheme.zeroIdealSheaf (Ramification.line f n) (Ramification.«section» f n))

/- Lemma 49.12.6 (3): the closed subscheme cut out by the Kähler different is locally
principal. -/
@[stacks 0BWJ] #check
  (AlgebraicGeometry.Scheme.Hom.different_isLocallyPrincipal :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
      [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
      [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left],
      IsLocallyPrincipalClosedSubscheme (subschemeι (kaehlerDifferent f.left)))

/- Lemma 49.12.6 (4): if `f` is étale at every associated point of `Y`, its different is an
effective Cartier divisor. -/
@[stacks 0BWJ] #check
  (AlgebraicGeometry.Scheme.Hom.different_isEffectiveCartier :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
      [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
      [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left]
      (h_assoc : ∀ y : Y.left, y ∈ Y.left.associatedPoints → f.left.EtaleAt y),
      IsEffectiveCartierDivisor (subschemeι (kaehlerDifferent f.left)))

/- Lemma 49.12.6 (5): if `f` is étale at every associated point of `Y`, tensoring the
pulled-back top differentials with the sheaf of the different gives the top differentials of
`Y` over `S`. -/
@[stacks 0BWJ] #check
  (AlgebraicGeometry.Scheme.Hom.topDifferentialsTensorDifferentIso :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (n : ℕ) {X Y : Over S} (f : Y ⟶ X)
      [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom]
      [LocallyOfFiniteType f.left] [LocallyQuasiFinite f.left]
      (h_assoc : ∀ y : Y.left, y ∈ Y.left.associatedPoints → f.left.EtaleAt y),
      Nonempty
        ((Λ[n] ((RingedSpace.Hom.pullback f.left.toShHom).obj Ω[X.hom.toShHom])) ⊗
            (@Scheme.IdealSheafData.associatedSheaf Y.left f.left.kaehlerDifferent
              (different_isEffectiveCartier n f h_assoc)) ≅
          Λ[n] Ω[Y.hom.toShHom]))

end AlgebraicGeometry.Scheme.Hom
