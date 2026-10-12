/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/-- The diagonal of `f`, regarded as a morphism to the top open of `X ×[S] X`. -/
def topDiagonal {X S : Scheme.{u}} (f : X ⟶ S) :
    X ⟶ (⊤ : (pullback f f).Opens).toScheme :=
  pullback.diagonal f ≫ (pullback f f).topIso.inv

/-- Composing `topDiagonal f` with the inclusion of the top open recovers the diagonal. -/
theorem topDiagonal_comp_ι {X S : Scheme.{u}} (f : X ⟶ S) :
    topDiagonal f ≫ (⊤ : (pullback f f).Opens).ι = pullback.diagonal f := sorry

/-- The top-open presentation of the diagonal of a separated morphism is a closed immersion. -/
noncomputable instance topDiagonalIsClosedImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] : IsClosedImmersion (topDiagonal f) := sorry

/-- Transpose a chosen diagonal-adjunction isomorphism to a map from the pushed-forward
diagonal algebra. -/
noncomputable def mapOfAdjointIso {X Y : Scheme.{u}} (δ : X ⟶ Y)
    [QuasiCompact δ] [QuasiSeparated δ]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (c : DerivedQCoh Y ⥤ DerivedQCoh X)
    (cAdjunction : DerivedQCoh.pushforwardCohomologyIn δ ⊣ c)
    (K : DerivedQCoh Y) (e : DerivedQCoh.structureSheaf X ≅ c.obj K) :
    (diagonalAlgebra δ).X ⟶ K.obj :=
  (RingedSpace.moduleDerivedPushforward δ.toShHom).map
      (((eqToHom (Mon.trivial_X
          (RingedSpace.ModuleDerived X.toRingedSpace)) :
            (Mon.trivial (RingedSpace.ModuleDerived X.toRingedSpace)).X ⟶
              𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)) ≫
        (DerivedQCoh.structureSheafUnitIso X).inv) ≫
        eqToHom (rfl : (DerivedQCoh.structureSheaf X).obj =
          (DerivedQCoh.inclusion X).obj (DerivedQCoh.structureSheaf X))) ≫
    (DerivedQCoh.pushforwardCohomologyIn.inclusionIso δ).inv.app
      (DerivedQCoh.structureSheaf X) ≫
    ((cAdjunction.homEquiv _ _).symm e.hom).hom

/-- `mapOfAdjointIso` is the ambient composite obtained from the structure-sheaf unit,
the pushforward comparison, and the adjunction transpose. -/
theorem mapOfAdjointIso_spec {X Y : Scheme.{u}} (δ : X ⟶ Y)
    [QuasiCompact δ] [QuasiSeparated δ]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (c : DerivedQCoh Y ⥤ DerivedQCoh X)
    (cAdjunction : DerivedQCoh.pushforwardCohomologyIn δ ⊣ c)
    (K : DerivedQCoh Y) (e : DerivedQCoh.structureSheaf X ≅ c.obj K) :
    mapOfAdjointIso δ c cAdjunction K e =
      (RingedSpace.moduleDerivedPushforward δ.toShHom).map
          (((eqToHom (Mon.trivial_X
              (RingedSpace.ModuleDerived X.toRingedSpace)) :
                (Mon.trivial (RingedSpace.ModuleDerived X.toRingedSpace)).X ⟶
                  𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)) ≫
            (DerivedQCoh.structureSheafUnitIso X).inv) ≫
            eqToHom (rfl : (DerivedQCoh.structureSheaf X).obj =
              (DerivedQCoh.inclusion X).obj (DerivedQCoh.structureSheaf X))) ≫
        (DerivedQCoh.pushforwardCohomologyIn.inclusionIso δ).inv.app
          (DerivedQCoh.structureSheaf X) ≫
        ((cAdjunction.homEquiv _ _).symm e.hom).hom := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
