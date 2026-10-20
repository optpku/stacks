/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.AddPoint
public import ReasLib.AlgebraicGeometry.Hilbert.SmoothProperCurve
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.SmoothCurve
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.AssociatedSheaf
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u
namespace AlgebraicGeometry.Hilbert

/-- The universal degree-`d` closed subscheme is the ideal of the universal Hilbert point. -/
def universalDivisor {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [(functor X d).IsRepresentable] :
    (pullback X.hom (functor X d).reprX.hom).IdealSheafData :=
  (functor X d).reprx.ideal

/-- The universal divisor is definitionally the ideal of the universal Hilbert point. -/
theorem universalDivisor_def {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [(functor X d).IsRepresentable] :
    universalDivisor X d = (functor X d).reprx.ideal := sorry

/-- The incidence morphism sends `(E, x)` to `(x, E + x)`. -/
def addPointIncidenceMap {S : Scheme.{u}} (X : Over S)
    [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    ((functor X d).reprX ⊗ X).left ⟶
      pullback X.hom (functor X (d + 1)).reprX.hom :=
  pullback.lift
    (CartesianMonoidalCategory.snd (functor X d).reprX X).left
    (addPointMap X d).left
    ((CartesianMonoidalCategory.snd (functor X d).reprX X).w.trans
      (addPointMap X d).w.symm)

/-- The first projection of the incidence morphism is the marked point. -/
theorem addPointIncidenceMap_fst {S : Scheme.{u}} (X : Over S)
    [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    addPointIncidenceMap X d ≫ pullback.fst X.hom (functor X (d + 1)).reprX.hom =
      (CartesianMonoidalCategory.snd (functor X d).reprX X).left := sorry

/-- The second projection of the incidence morphism adds the marked point. -/
theorem addPointIncidenceMap_snd {S : Scheme.{u}} (X : Over S)
    [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    addPointIncidenceMap X d ≫ pullback.snd X.hom (functor X (d + 1)).reprX.hom =
      (addPointMap X d).left := sorry

/-- The incidence morphism is a closed immersion. -/
theorem addPointIncidenceMap_isClosedImmersion {S : Scheme.{u}} (X : Over S)
    [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    IsClosedImmersion (addPointIncidenceMap X d) := sorry

/-- The universal successor-degree divisor is relative effective Cartier. -/
theorem universalDivisor_isRelativeEffectiveCartier
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    IsRelativeEffectiveCartierDivisor
      (pullback.snd X.hom (functor X (d + 1)).reprX.hom)
      (universalDivisor X (d + 1)) := sorry

/-- The universal successor-degree divisor is effective Cartier. -/
theorem universalDivisor_isEffectiveCartier
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    IsEffectiveCartierDivisor (universalDivisor X (d + 1)).subschemeι := sorry

/-- The incidence morphism has the universal divisor as its defining ideal. -/
theorem universalDivisor_eq_addPointIncidenceMap_ker
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    universalDivisor X (d + 1) = (addPointIncidenceMap X d).ker := sorry

/-- The universal divisor scheme is isomorphic to the degree-`d` product with the curve. -/
theorem universalDivisorSubscheme_isIsomorphic
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    IsIsomorphic (universalDivisor X (d + 1)).subscheme
      ((functor X d).reprX ⊗ X).left := sorry

/-- The sheaf associated to the universal divisor is denoted `𝒪(D_univ)`. -/
abbrev universalDivisorSheaf
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    (pullback X.hom (functor X (d + 1)).reprX.hom).Modules :=
  @AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf _
    (universalDivisor X (d + 1)) (universalDivisor_isEffectiveCartier X d)

/-- The sheaf associated to the universal divisor is invertible. -/
theorem universalDivisorSheaf_isInvertible
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    Scheme.Modules.Invertible (universalDivisorSheaf X d) := sorry

/-- The pullback of the universal divisor to a rational point is effective Cartier. -/
theorem universalDivisorFiber_isEffectiveCartier
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ)
    (x : (Over.mk (𝟙 (Spec (CommRingCat.of k))) : SchemeOverField k) ⟶
      (functor X (d + 1)).reprX) :
    IsEffectiveCartierDivisor
      ((universalDivisor X (d + 1)).comap (fiberMap X x)).subschemeι := sorry

/-- The fibre ideal equals the ideal classified by its rational Hilbert point. -/
theorem universalDivisor_fiber_ideal
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ)
    (x : (Over.mk (𝟙 (Spec (CommRingCat.of k))) : SchemeOverField k) ⟶
      (functor X (d + 1)).reprX) :
    (universalDivisor X (d + 1)).comap (fiberMap X x) =
      ((functor X (d + 1)).representableBy.homEquiv x).ideal := sorry

/-- The canonical pullback isomorphism identifies the fibre sheaf with the comapped sheaf. -/
noncomputable def universalDivisorFiberIso
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ)
    (x : (Over.mk (𝟙 (Spec (CommRingCat.of k))) : SchemeOverField k) ⟶
      (functor X (d + 1)).reprX) :
    (Scheme.Modules.pullback (fiberMap X x)).obj
        (universalDivisorSheaf X d) ≅
      @AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf _
        ((universalDivisor X (d + 1)).comap (fiberMap X x))
        (universalDivisorFiber_isEffectiveCartier X d x) :=
  @AlgebraicGeometry.Scheme.IdealSheafData.associatedSheafPullbackIso _ _
    (universalDivisor X (d + 1)) (fiberMap X x)
    (universalDivisor_isEffectiveCartier X d)
    (universalDivisorFiber_isEffectiveCartier X d x)

/-- The fibre isomorphism is the canonical associated-sheaf pullback isomorphism. -/
theorem universalDivisorFiberIso_def
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ)
    (x : (Over.mk (𝟙 (Spec (CommRingCat.of k))) : SchemeOverField k) ⟶
      (functor X (d + 1)).reprX) :
    universalDivisorFiberIso X d x =
      @AlgebraicGeometry.Scheme.IdealSheafData.associatedSheafPullbackIso _ _
        (universalDivisor X (d + 1)) (fiberMap X x)
        (universalDivisor_isEffectiveCartier X d)
        (universalDivisorFiber_isEffectiveCartier X d x) := sorry

/-- The fibre sheaf is isomorphic to the associated sheaf of the classified ideal. -/
theorem universalDivisorFiber_isIsomorphic_classifiedSheaf
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ)
    (x : (Over.mk (𝟙 (Spec (CommRingCat.of k))) : SchemeOverField k) ⟶
      (functor X (d + 1)).reprX) :
    IsIsomorphic
      ((Scheme.Modules.pullback (fiberMap X x)).obj (universalDivisorSheaf X d))
      (@AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf _
        ((functor X (d + 1)).representableBy.homEquiv x).ideal
        ((universalDivisor_fiber_ideal X d x) ▸
          (universalDivisorFiber_isEffectiveCartier X d x))) := sorry

end AlgebraicGeometry.Hilbert
