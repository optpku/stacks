/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeFiltration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Basic
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The line-bundle projection commutes with the structural morphism to the base. -/
theorem associatedLineBundleSquare_w {S X : Scheme.{u}} (f : X ⟶ S)
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ)) [IsRelativeSpectrumOver P] :
    (associatedVectorBundleπ ℒ P).toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      (associatedVectorBundleπ ℒ P ≫ f).toLRSHom.toShHom ≫ 𝟙 _ := sorry

/-- For a morphism from the base to `Spec ℚ`, the relative de Rham comparison map of a line
bundle is a quasi-isomorphism. -/
theorem associatedLineBundleDeRhamComparison_quasiIso
    {S X : Scheme.{u}}
    (g : S ⟶ Spec (CommRingCat.of (ULift.{u} ℚ))) (f : X ⟶ S)
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ)) [IsRelativeSpectrumOver P] :
    QuasiIso
      (RingedSpace.DeRham.map
        (CommSq.mk (associatedLineBundleSquare_w f ℒ P))) := sorry

/-- For a morphism from the base to `Spec ℚ`, the relative de Rham cohomology of a line bundle's
total space agrees with that of its base in every degree. -/
theorem associatedLineBundleDeRhamCohomology_isomorphic
    {S X : Scheme.{u}}
    (g : S ⟶ Spec (CommRingCat.of (ULift.{u} ℚ))) (f : X ⟶ S)
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ)) [IsRelativeSpectrumOver P]
    (n : ℤ) :
    IsIsomorphic (AddCommGrpCat.of (cohomology f n))
      (AddCommGrpCat.of (cohomology (associatedVectorBundleπ ℒ P ≫ f) n)) := sorry

end AlgebraicGeometry.Scheme.DeRham
