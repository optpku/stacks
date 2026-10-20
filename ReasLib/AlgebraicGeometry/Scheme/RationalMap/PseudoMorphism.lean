/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure.Reduced

@[expose] public section

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A pseudo-partial map is a morphism defined on a scheme-theoretically dense open
subscheme of its source. -/
structure PseudoPartialMap (X Y : Scheme.{u}) where
  /-- The open domain on which the pseudo-partial map is defined. -/
  domain : X.Opens
  /-- The domain of a pseudo-partial map is scheme-theoretically dense. -/
  schemeTheoreticallyDense_domain : schemeTheoreticallyDense domain
  /-- The morphism defined on the open domain. -/
  hom : domain.toScheme ⟶ Y

namespace PseudoPartialMap

/-- Restrict a pseudo-partial map to a scheme-theoretically dense open subdomain. -/
def restrict {X Y : Scheme.{u}} (f : PseudoPartialMap X Y) (U : X.Opens)
    (hU : schemeTheoreticallyDense U) (hU' : U ≤ f.domain) : PseudoPartialMap X Y where
  domain := U
  schemeTheoreticallyDense_domain := hU
  hom := X.homOfLE hU' ≫ f.hom

/-- Two pseudo-partial maps agree when their morphisms coincide on a common
scheme-theoretically dense open subdomain. -/
protected def equiv {X Y : Scheme.{u}} (f g : PseudoPartialMap X Y) : Prop :=
  ∃ W : X.Opens, schemeTheoreticallyDense W ∧
    ∃ (hWl : W ≤ f.domain) (hWr : W ≤ g.domain),
      X.homOfLE hWl ≫ f.hom = X.homOfLE hWr ≫ g.hom

/-- Agreement on a scheme-theoretically dense open subdomain is an equivalence relation. -/
theorem equivalence_rel (X Y : Scheme.{u}) :
    Equivalence (@PseudoPartialMap.equiv X Y) := sorry

/-- The setoid of pseudo-partial maps under agreement on a scheme-theoretically dense
open subdomain. -/
def setoid (X Y : Scheme.{u}) : Setoid (PseudoPartialMap X Y) where
  r := PseudoPartialMap.equiv
  iseqv := equivalence_rel X Y

end PseudoPartialMap

/-- A pseudo-morphism is an equivalence class of morphisms defined on
scheme-theoretically dense open subschemes. -/
def PseudoMorphism (X Y : Scheme.{u}) : Type u :=
  Quotient (PseudoPartialMap.setoid X Y)

namespace PseudoPartialMap

/-- The pseudo-morphism represented by a pseudo-partial map. -/
def toPseudoMorphism {X Y : Scheme.{u}} (f : PseudoPartialMap X Y) : PseudoMorphism X Y :=
  Quotient.mk _ f

end PseudoPartialMap

namespace PseudoMorphism

/-- Every pseudo-morphism has a pseudo-partial-map representative. -/
theorem exists_rep {X Y : Scheme.{u}} (f : PseudoMorphism X Y) :
    ∃ g : PseudoPartialMap X Y, g.toPseudoMorphism = f := sorry

end PseudoMorphism

namespace PseudoPartialMap

/-- A pseudo-partial map from a reduced scheme determines an ordinary partial map. -/
def toPartialMap {X Y : Scheme.{u}} [IsReduced X] (f : PseudoPartialMap X Y) :
    X.PartialMap Y where
  domain := f.domain
  dense_domain :=
    (SchemeTheoreticClosure.dense_iff_schemeTheoreticallyDense_of_isReduced f.domain).mpr
      f.schemeTheoreticallyDense_domain
  hom := f.hom

/-- For a reduced source, pseudo-partial-map agreement is equivalent to ordinary
partial-map agreement. -/
theorem equiv_iff_toPartialMap_equiv_of_isReduced {X Y : Scheme.{u}} [IsReduced X]
    (f g : PseudoPartialMap X Y) :
    f.equiv g ↔ f.toPartialMap.equiv g.toPartialMap := sorry

end PseudoPartialMap

namespace PseudoMorphism

/-- A pseudo-morphism from a reduced scheme determines an ordinary rational map. -/
def toRationalMap {X Y : Scheme.{u}} [IsReduced X] :
    PseudoMorphism X Y → RationalMap X Y :=
  Quotient.lift (fun f ↦ f.toPartialMap.toRationalMap)
    (fun f g h ↦ PartialMap.toRationalMap_eq_iff.mpr
      ((PseudoPartialMap.equiv_iff_toPartialMap_equiv_of_isReduced f g).mp h))

/-- The rational map of a represented pseudo-morphism is the rational map of its
pseudo-partial-map representative. -/
theorem toRationalMap_toPseudoMorphism {X Y : Scheme.{u}} [IsReduced X]
    (f : PseudoPartialMap X Y) :
    toRationalMap f.toPseudoMorphism = f.toPartialMap.toRationalMap := sorry

/-- For a reduced source, pseudo-morphisms and ordinary rational maps are in bijection. -/
theorem toRationalMap_bijective_of_isReduced {X Y : Scheme.{u}} [IsReduced X] :
    Function.Bijective (toRationalMap : PseudoMorphism X Y → RationalMap X Y) := sorry

end PseudoMorphism

end AlgebraicGeometry.Scheme
