/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.LocallyShiftedSingle
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.LocalConcentrationAt
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FlatQuasiFinite

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- For a Cohen–Macaulay morphism, the compactification model of the upper-shriek
dualizing object is locally a coherent relative-flat module shifted by the locally
constant relative dimension. -/
theorem exists_dualizingModule_of_cohenMacaulay
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    ∃ d : LocallyConstant X.obj.left ℕ,
      ∃ ω : RingedSpace.Modules (LocallyRingedSpace.toRingedSpace
          (Scheme.toLocallyRingedSpace X.obj.left)),
        (∀ x : X.obj.left,
          fiberDimensionAt f.hom.left x = (d x : WithBot ℕ∞)) ∧
        ω.IsCoherent ∧
        SheafOfModules.IsFlatOver ω
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f.hom.left)) ∧
        RingedSpace.ModuleDerived.IsLocallyShiftedSingle
          (dualizingObject f P A).obj ω d := sorry

/-- A flat finite-type-separated morphism is Cohen–Macaulay at a point exactly
when its compactification upper-shriek dualizing object is locally concentrated
in one degree near that point. -/
theorem cohenMacaulayAt_iff_isLocallyConcentratedAt
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) (x : X.obj.left) :
    CohenMacaulayAt f.hom.left x ↔
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyConcentratedAt
        (dualizingObject f P A).obj x := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
