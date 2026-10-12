/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Relative morphisms from finite locally free schemes

This module records representability criteria for relative-Hom presheaves with
a finite locally free source, including affine targets and targets admitting
common affine neighborhoods for finite subsets of their fibres.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/-- If `Z` is finite locally free over `S` and `X` is affine over `S`, then the
relative-Hom presheaf associated to `Z` and `X` is represented by a scheme
affine over `S`. -/
theorem representableByAffineOfFiniteLocallyFree {S : Scheme.{u}} (Z X : Over S)
    [IsFiniteLocallyFree Z.hom] [IsAffineHom X.hom] :
    ∃ (H : Over S) (hH : IsAffineHom H.hom),
      Nonempty ((functor Z X).RepresentableBy H) := sorry

/-- If `Z` is finite locally free over `S` and every finite set of points of `X`
over a common point of `S` lies in an affine open of `X`, then the relative-Hom
presheaf associated to `Z` and `X` is representable by a scheme over `S`. -/
theorem representableOfFiniteLocallyFree {S : Scheme.{u}} (Z X : Over S)
    [IsFiniteLocallyFree Z.hom]
    (hX : ∀ (s : S) (E : Set X.left), E.Finite →
      (∀ x ∈ E, X.hom x = s) →
      ∃ U : X.left.affineOpens, E ⊆ ((U : X.left.Opens) : Set X.left)) :
    ∃ H : Over S, Nonempty ((functor Z X).RepresentableBy H) := sorry

end AlgebraicGeometry.Scheme.RelativeHom
