/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Points
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom AlgebraicGeometry.RingedSpace.Module.Skyscraper
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A singular proper genus-zero curve with ground-field global functions is obtained
from a projective line over a nontrivial finite extension by identifying rational
points, with the resulting structure-sheaf quotient supported at the identified
point. -/
theorem exists_projectiveLineNormalization
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (h_singular : ¬ Scheme.Regular X.left) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k')
      (h_nontrivial : ¬ Function.Surjective (algebraMap k k'))
      (X' : SchemeOverField k')
      (h_projectiveLine : Nonempty (X' ≅ ProjectiveSpace.schemeOver k' 1))
      (ν : X'.left ⟶ X.left)
      (x' : SchemeOverField.point k' ⟶ X')
      (x : SchemeOverField.point k ⟶ X)
      (h_base : X'.hom ≫ FieldExtension.specMap k k' = ν ≫ X.hom)
      (h_point : SchemeOverField.rationalPoint x' ≫ ν =
        FieldExtension.specMap k k' ≫ SchemeOverField.rationalPoint x)
      (h_x_singular : ¬ IsRegularLocalRing
        (stalkRing X
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))))
      (U : X.left.Opens) (U' : X'.left.Opens)
      (hU : (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
      (hU' : (U' : Set X'.left) =
        {SchemeOverField.rationalPoint x' (IsLocalRing.closedPoint k')}ᶜ)
      (h_preimage : ν ⁻¹ᵁ U = U')
      (h_restrict : IsIso (ν ∣_ U))
      (q : (Scheme.Modules.pushforward ν).obj
          (SheafOfModules.unit X'.left.ringCatSheaf : X'.left.Modules) ⟶
        atPoint
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
          ((ModuleCat.restrictScalars
            (Scheme.stalkClosedPointTo
              (SchemeOverField.rationalPoint x)).hom).obj
            (ModuleCat.of k
              (k' ⧸ LinearMap.range (Algebra.linearMap k k')))))
      (h_zero : SheafOfModules.unitToPushforwardObjUnit
          (toRingCatSheafHom ν.toShHom) ≫ q = 0),
      (ShortComplex.mk
        (SheafOfModules.unitToPushforwardObjUnit
          (toRingCatSheafHom ν.toShHom)) q h_zero).ShortExact := sorry

end AlgebraicGeometry.SchemeOverField
