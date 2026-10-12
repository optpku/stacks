/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex

universe u

namespace AlgebraicGeometry.IsModification

/-- For a normal modification of a two-dimensional normal Nagata local base with a chosen
dualizing complex, a relatively normalized dualizing module has vanishing first higher
direct image. -/
theorem higherDirectImageOne_dualizingModule_isZero
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [_root_.IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsModification f] (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)))
    (hX : X.isNormal)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsDualizingComplex HA)
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS ((affineTildeDerived A).obj (ωA⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωX : X.Modules)
    (hωX : RingedSpace.ModuleDerived.IsDualizingModule
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) HX
      (-(2 : ℤ)) ωX)
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)) :
    IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom ωX 1) := sorry

end AlgebraicGeometry.IsModification
