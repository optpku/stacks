/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.ProjectionFormula
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.LocallyShiftedSingle
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.PresentationDeterminant
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

open RingedSpace.ModuleDerived

/-- For a local complete-intersection morphism with an immersion/proper-smooth
factorization, the relative differentials admit a fundamental-class map to a
locally shifted-single upper-shriek dualizing module, with the stalkwise
isomorphism criterion given by smoothness. -/
theorem existsFundamentalClass
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.hom.left]
    {P : Scheme.{u}} (i : X.obj.left ⟶ P) (g : P ⟶ Y.obj.left)
    (factorization : i ≫ g = f.hom.left)
    [IsImmersion i] [IsProper g] [Smooth g]
    (Q : Compactification.Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (Compactification.Of.ambientMorphism Q))
    (r : LocallyConstant X.obj.left ℕ)
    (ω : RingedSpace.Modules (LocallyRingedSpace.toRingedSpace
      (Scheme.toLocallyRingedSpace X.obj.left)))
    (hω : IsLocallyShiftedSingle (dualizingObject f Q A).obj ω r) :
    ∃ φ : ∀ n : ℕ,
        (Λ[n] ((RingedSpace.moduleRestrictionToOpen (LocallyRingedSpace.toRingedSpace
          (Scheme.toLocallyRingedSpace X.obj.left))
          (r.fiberClopen n).toOpens).obj
            Ω[LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f.hom.left)])) ⟶
            (RingedSpace.moduleRestrictionToOpen (LocallyRingedSpace.toRingedSpace
              (Scheme.toLocallyRingedSpace X.obj.left))
              (r.fiberClopen n).toOpens).obj ω,
      ∀ (n : ℕ) (x : (r.fiberClopen n).toOpens),
        IsIso (RingedSpace.moduleStalkHom x (φ n)) ↔
            AlgebraicGeometry.Scheme.Hom.SmoothAt f.hom.left x.1 := sorry

/-- Under a Cohen–Macaulay target and low-dimensional Koszul hypotheses, a
fundamental class map exists for a morphism with constant generic relative
transcendence degree and an immersion/proper-smooth factorization. -/
theorem existsFundamentalClass_of_koszulAt_le_one
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [Scheme.CohenMacaulay Y.obj.left]
    {P : Scheme.{u}} (i : X.obj.left ⟶ P) (g : P ⟶ Y.obj.left)
    (factorization : i ≫ g = f.hom.left)
    [IsImmersion i] [IsProper g] [Smooth g]
    (Q : Compactification.Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (Compactification.Of.ambientMorphism Q))
    (r : ℕ)
    (hKoszul : ∀ x : X.obj.left,
      ringKrullDim ((X.obj.left).presheaf.stalk x) ≤ 1 → KoszulAt f.hom.left x)
    (htrdeg : ∀ ξ : X.obj.left,
      ξ ∈ genericPoints X.obj.left → residueFieldTrdegAt f.hom.left ξ = r) :
    ∃ φ : (Λ[r] Ω[LocallyRingedSpace.Hom.toShHom
        (Scheme.Hom.toLRSHom f.hom.left)]) ⟶
        cohomologySheaf (dualizingObject f Q A).obj (-(r : ℤ)),
      ∀ x : X.obj.left,
        SmoothAt f.hom.left x → IsIso (RingedSpace.moduleStalkHom x φ) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
