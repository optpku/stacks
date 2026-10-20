module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Linearity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Stalk

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- A relatively linear functor is affine-open coproduct-linear when it preserves arbitrary
coproducts, is right exact after affine-open pushforward, and sends stalkwise split short exact
sequences to short complexes that are exact with monic first map. -/
class AffineOpenCoproductLinear (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) : Prop
    extends LinearOver x y F where
  preservesCoproducts : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F
  affineOpen_rightExact :
    ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsAffine U] [IsOpenImmersion j]
      [QuasiCompact j] [QuasiSeparated j],
      rightExactFunctor (Scheme.QCoh U) (Scheme.QCoh Y)
        (Scheme.QCoh.pushforward j ⋙ F)
  preservesStalkwiseSplitExact :
    ∀ (S : ShortComplex (Scheme.QCoh X)), IsStalkwiseSplitExact S →
      Mono (F.map S.f) ∧ (S.map F).Exact

/-- For an additive functor, affine-open coproduct-linearity is equivalent to relative
linearity, coproduct preservation, affine-open right exactness, and preservation of initial
exactness for stalkwise split short exact sequences. -/
theorem affineOpenCoproductLinear_iff (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y)
    [F.Additive] :
    AffineOpenCoproductLinear x y F ↔
      LinearOver x y F ∧
        (∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) ∧
          (∀ {U : Scheme.{u}} (j : U ⟶ X) [IsAffine U] [IsOpenImmersion j]
            [QuasiCompact j] [QuasiSeparated j],
            rightExactFunctor (Scheme.QCoh U) (Scheme.QCoh Y)
              (Scheme.QCoh.pushforward j ⋙ F)) ∧
            ∀ (S : ShortComplex (Scheme.QCoh X)), IsStalkwiseSplitExact S →
              Mono (F.map S.f) ∧ (S.map F).Exact := by
  constructor
  · intro h
    exact ⟨h.toLinearOver, h.preservesCoproducts, h.affineOpen_rightExact,
      h.preservesStalkwiseSplitExact⟩
  · rintro ⟨hlinear, hcoproducts, hopen, hsplit⟩
    exact
      { toLinearOver := hlinear
        preservesCoproducts := hcoproducts
        affineOpen_rightExact := hopen
        preservesStalkwiseSplitExact := hsplit }

/-- The full subcategory of affine-open coproduct-linear functors between quasicoherent
module categories over a fixed affine base. -/
abbrev AffineOpenCoproductLinearFunctor (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) :=
  ObjectProperty.FullSubcategory
    fun F : Scheme.QCoh X ⥤ Scheme.QCoh Y ↦ AffineOpenCoproductLinear x y F

/-- An object of the category of affine-open coproduct-linear functors has the defining
affine-open coproduct-linearity property. -/
instance affineOpenCoproductLinearFunctor_property
    (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
    (F : AffineOpenCoproductLinearFunctor x y) :
    AffineOpenCoproductLinear x y F.obj := F.property

end AlgebraicGeometry.Scheme.QCoh
