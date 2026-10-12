/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.RingTheory.Excellent

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a finite type morphism from a normal scheme to an excellent regular
scheme over a field, the inclusion of the maximal étale source open is affine. -/
theorem isAffineHom_etaleSourceLocus_ι
    {k : Type u} [Field k] {Y : Scheme.{u}} [Scheme.Regular Y]
    [Y.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsExcellentRing A)]
    (hY : Y ⟶ Spec (CommRingCat.of k)) {X : Scheme.{u}} (f : X ⟶ Y)
    [Scheme.Hom.FiniteType f] (hX : X.isNormal) :
    IsAffineHom
      (MorphismProperty.sourceLocus (fun ⦃X Y : Scheme.{u}⦄ (g : X ⟶ Y) ↦ Etale g) f).ι := sorry

end AlgebraicGeometry.Scheme.Hom
