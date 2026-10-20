/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex

/-! Relative normalization of dualizing complexes along finite-type morphisms. -/

/-- A fixed complex `ωX` is normalized relative to `ωS` along `f` when it is the complex of a
chosen finite-cover normalization package. -/
def RelativeTo {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  ∃ cover : FiniteSeparatedOpenCover f,
    ∃ duality : ExceptionalInverseImageSetup f cover,
      ∃ K : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality,
        K.complex = ωX

/-- The fixed-complex predicate is equivalent to the existence of chosen finite-cover
normalization data with the prescribed complex. -/
theorem relativeTo_iff_exists_onCover {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace) :
    RelativeTo f HS HX ωS hωS ωX ↔
      ∃ cover : FiniteSeparatedOpenCover f,
        ∃ duality : ExceptionalInverseImageSetup f cover,
          ∃ K : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality,
            K.complex = ωX := sorry

namespace RelativeTo

open RingedSpace.ModuleDerived

/-- Chosen finite-cover normalization data gives normalization of its underlying complex. -/
theorem ofOnCover {S X : Scheme.{u}} [IsNoetherian S]
    {f : X ⟶ S} [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    {HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex HS}
    {cover : FiniteSeparatedOpenCover f} {duality : ExceptionalInverseImageSetup f cover}
    (K : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality) :
    RelativeTo f HS HX ωS hωS K.complex := sorry

/-- A complex normalized relative to a dualizing complex is itself dualizing. -/
theorem isDualizing {S X : Scheme.{u}} [IsNoetherian S]
    {f : X ⟶ S} [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    {HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex HS}
    {ωX : RingedSpace.ModuleDerived X.toRingedSpace}
    (hωX : RelativeTo f HS HX ωS hωS ωX) :
    ωX.IsDualizingComplex HX := sorry

/-- Normalization is transitive along a morphism in the finite-type slice over a Noetherian base. -/
theorem trans {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) :
    let X' : Scheme := X.obj.left
    let Y' : Scheme := Y.obj.left
    let f' : X' ⟶ Y' := f.hom.left
    ∀ [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
      (HY : MonoidalClosed (RingedSpace.ModuleDerived Y'.toRingedSpace))
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
      (ωX : RingedSpace.ModuleDerived X'.toRingedSpace)
      (ωY : RingedSpace.ModuleDerived Y'.toRingedSpace)
      (hX : @RelativeTo _ _ _ X.obj.hom
        (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX)
      (hY : @RelativeTo _ _ _ Y.obj.hom
        (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY),
      @RelativeTo _ _ _ f' (FiniteTypeOver.instFiniteTypeHom f) _ HY _ HX ωY
        (@RelativeTo.isDualizing _ _ _ Y.obj.hom (FiniteTypeOver.instFiniteType Y)
          _ HS _ HY ωS hωS ωY hY : ωY.IsDualizingComplex HY) ωX := sorry

/-- Relative normalization transfers normalized dualizing stalks between closed points of a
finite-type morphism over a Noetherian scheme. -/
theorem stalk_isNormalizedDualizingComplex_of_closedPoint
    {S : Scheme.{u}} [IsNoetherian S] (X : Scheme.FiniteTypeOver S)
    (x : X.obj.left) (s : S) (hx : x ∈ closedPoints X.obj.left)
    (hs : s ∈ closedPoints S) (hxs : X.obj.hom x = s)
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.obj.left.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace))
    [MonoidalCategory (DerivedCategory (ModuleCat (S.presheaf.stalk s)))]
    (Hs : MonoidalClosed (DerivedCategory (ModuleCat (S.presheaf.stalk s))))
    [MonoidalCategory (DerivedCategory (ModuleCat (X.obj.left.presheaf.stalk x)))]
    (Hx : MonoidalClosed (DerivedCategory (ModuleCat (X.obj.left.presheaf.stalk x))))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.obj.left.toRingedSpace)
    (hωX : @RelativeTo _ _ _ X.obj.hom (FiniteTypeOver.instFiniteType X)
      _ HS _ HX ωS hωS ωX)
    (hωS_s : (Stalk.obj ωS s).IsNormalizedDualizingComplex Hs) :
    (Stalk.obj ωX x).IsNormalizedDualizingComplex Hx := sorry

end RelativeTo

end AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
