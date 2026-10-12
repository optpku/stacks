/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction

/-!
# Normalized dualizing complexes and proper right adjoints

This module relates normalized dualizing complexes to right adjoints of derived
quasicoherent pushforward along proper morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo

/-- A right adjoint to derived quasicoherent pushforward along a proper morphism sends a
normalized dualizing complex on the target to a normalized dualizing complex on the source,
up to isomorphism. -/
theorem isIsomorphic_rightAdjoint_of_isProper
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left] :
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
      (ωX : Scheme.DerivedQCoh X') (ωY : Scheme.DerivedQCoh Y')
      (hX : @RelativeTo _ _ _ X.obj.hom (Scheme.FiniteTypeOver.instFiniteType X)
        _ HS _ HX ωS hωS ωX.obj)
      (hY : @RelativeTo _ _ _ Y.obj.hom (Scheme.FiniteTypeOver.instFiniteType Y)
        _ HS _ HY ωS hωS ωY.obj)
      (a : Scheme.DerivedQCoh Y' ⥤ Scheme.DerivedQCoh X')
      (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f' ⊣ a),
      IsIsomorphic (a.obj ωY) ωX := sorry

end AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
