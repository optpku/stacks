module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Locus

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme.Hom TopologicalSpace
open Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme
namespace Compactification.Of.UpperShriek

/-- For a flat morphism between finite-type separated schemes over a Noetherian
scheme, Gorensteinness at a point is equivalent to local shifted invertibility
of the compactification upper-shriek dualizing object. -/
theorem gorensteinAt_iff_exists_open_isLocallyShiftedInvertible
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) (x : X.obj.left) :
    gorensteinAt f.hom.left x ↔
      ∃ U : Opens X.obj.left, x ∈ U ∧
        RingedSpace.ModuleDerived.IsLocallyShiftedInvertible
          (((DerivedQCoh.OpenImmersion.pullback U.ι).obj
            (dualizingObject f P A)).obj) := sorry

end Compactification.Of.UpperShriek

namespace Hom

/-- For a flat morphism between finite-type separated schemes over a Noetherian
scheme, the locus where the morphism is Gorenstein is open. -/
theorem isOpen_gorensteinLocus
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left] :
    IsOpen (gorensteinLocus f.hom.left) := sorry

end Hom
end AlgebraicGeometry.Scheme
