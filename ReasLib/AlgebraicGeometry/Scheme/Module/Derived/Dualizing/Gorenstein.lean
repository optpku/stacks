/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Gorenstein

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.KFlat
open DerivedCategory.DerivedTensor.Right.Monoidal

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- A locally Noetherian scheme carrying a dualizing complex is Gorenstein exactly when that
complex is tensor-invertible in its derived category. -/
theorem gorenstein_iff_isInvertibleObject
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    Scheme.Gorenstein X ↔ MonoidalCategory.isInvertibleObject ω := sorry

/-- The local ring at `x` is Gorenstein exactly when the derived stalk of a dualizing complex at
`x` is tensor-invertible. -/
theorem stalk_gorenstein_iff_isInvertibleObject
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) (x : X)
    [MonoidalCategory (DerivedCategory (ModuleCat (X.presheaf.stalk x)))]
    (T : @Model (ModuleCat (X.presheaf.stalk x)) _ _ _ _ _ _ _) :
    IsGorensteinLocalRing (X.presheaf.stalk x) ↔
      MonoidalCategory.isInvertibleObject (Stalk.obj ω x) := sorry

/-- The locus where the local rings of a locally Noetherian scheme with a dualizing complex are
Gorenstein is open. -/
theorem isOpen_gorensteinLocus
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    IsOpen (Scheme.gorensteinLocus X) := sorry

/-- The open subset cut out by the Gorenstein locus of a chosen dualizing complex. -/
def gorensteinOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    X.Opens :=
  ⟨Scheme.gorensteinLocus X, hω.isOpen_gorensteinLocus⟩

/-- The carrier of `gorensteinOpen` is the Gorenstein locus. -/
theorem coe_gorensteinOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    (hω.gorensteinOpen : Set X) = Scheme.gorensteinLocus X := sorry

/-- The open subscheme on the Gorenstein locus is Gorenstein. -/
theorem gorensteinOpen_isGorenstein
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    Scheme.Gorenstein hω.gorensteinOpen.toScheme := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex

namespace AlgebraicGeometry.Scheme.Gorenstein

/-- On a Gorenstein scheme, a dualizing complex exists exactly when the structure sheaf in degree
zero is dualizing. -/
theorem exists_iff_structureSheaf
    {X : Scheme.{u}} [Scheme.Gorenstein X] :
    (∃ K : RingedSpace.ModuleDerived X.toRingedSpace, Scheme.IsDualizingComplex K) ↔
      Scheme.IsDualizingComplex (Scheme.DerivedQCoh.structureSheaf X).obj := sorry

end AlgebraicGeometry.Scheme.Gorenstein
