/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Blowup.Triangle

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.Cohomology

universe u

namespace AlgebraicGeometry.IsBlowup.DeRham

variable {S X X' : Scheme.{u}}

/-- Direct image along the coefficient-site morphism of a blowup admits a total right
derived functor on module sheaves. -/
instance toBlowupHasRightDerived
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom (relativeStructureSquare f I b)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom)) :=
  modulePushforwardToDerived.hasRightDerived (coefficientHom (relativeStructureSquare f I b))

/-- For a blowup of a smooth scheme over `S` along a center smooth over `S`, the canonical
relative de Rham comparison admits a retraction in the derived category of modules over
the inverse-image coefficient sheaf on `X`. -/
@[instance]
theorem toBlowup_isSplitMono
    (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] :
    IsSplitMono (toBlowup f I b) := sorry

end AlgebraicGeometry.IsBlowup.DeRham
