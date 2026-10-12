/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.RightAdjoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.20.8: if `f : X ⟶ Y` is proper between schemes of finite type over a
Noetherian scheme `S`, then any right adjoint to derived quasicoherent pushforward sends a
dualizing complex on `Y` normalized relative to `ωS` to the similarly normalized complex on
`X`, up to canonical isomorphism. -/
@[stacks 0AUD] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isIsomorphic_rightAdjoint_of_isProper :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
      {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [AlgebraicGeometry.IsProper f.hom.left],
      let X' : Scheme := X.obj.left
      let Y' : Scheme := Y.obj.left
      let f' : X' ⟶ Y' := f.hom.left
      ∀ [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)]
        (HS : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace))
        [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived X'.toRingedSpace)]
        (HX : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X'.toRingedSpace))
        [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived Y'.toRingedSpace)]
        (HY : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived Y'.toRingedSpace))
        (ωS : AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)
        (hωS : ωS.IsDualizingComplex HS)
        (ωX : AlgebraicGeometry.Scheme.DerivedQCoh X')
        (ωY : AlgebraicGeometry.Scheme.DerivedQCoh Y')
        (hX : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _
          X.obj.hom (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX
          ωS hωS ωX.obj)
        (hY : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _
          Y.obj.hom (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY
          ωS hωS ωY.obj)
        (a : AlgebraicGeometry.Scheme.DerivedQCoh Y' ⥤
          AlgebraicGeometry.Scheme.DerivedQCoh X')
        (aAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f' ⊣ a),
        IsIsomorphic (a.obj ωY) ωX)
