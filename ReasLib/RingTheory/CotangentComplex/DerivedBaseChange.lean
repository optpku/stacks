module

public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.DerivedBaseChange

/-!
# Derived base change of cotangent complexes

A commutative square of rings gives a canonical comparison from derived scalar
extension of the cotangent complex to the cotangent complex over the new base.
This comparison is invertible when the square induces a derived-tensor
quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory
open RingedSite.Cotangent.Functoriality

universe u

noncomputable section

namespace Algebra.CotangentComplex

variable {A B A' B' : CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/-- The canonical morphism `L_{B/A} ⊗[B]^L B' ⟶ L_{B'/A'}` induced by a
commutative square of ring maps. -/
def mapDerived (sq : CommSq ρ α β φ) :
    (ModuleCat.derivedExtensionOfScalars φ.hom).obj
        (DerivedCategory.Q.obj (RingHom.cotangentComplex α.hom)) ⟶
      DerivedCategory.Q.obj (RingHom.cotangentComplex β.hom) :=
  (ModuleCat.derivedExtensionComplexCounit φ.hom).app
      (RingHom.cotangentComplex α.hom) ≫
    DerivedCategory.Q.map
      (map α.hom β.hom ρ.hom φ.hom
        (congrArg (fun f : A ⟶ B' => f.hom) sq.w))

/-- The derived cotangent comparison is the derived-extension cochain counit
followed by the localization of the cochain-level functoriality map. -/
theorem mapDerived_eq (sq : CommSq ρ α β φ) :
    mapDerived sq =
      (ModuleCat.derivedExtensionComplexCounit φ.hom).app
          (RingHom.cotangentComplex α.hom) ≫
        DerivedCategory.Q.map
          (map α.hom β.hom ρ.hom φ.hom
            (congrArg (fun f : A ⟶ B' => f.hom) sq.w)) :=
  rfl

/-- If a commutative square induces a quasi-isomorphism `B ⊗[A]^L A' → B'`,
then its canonical cotangent comparison `L_{B/A} ⊗[B]^L B' ⟶ L_{B'/A'}`
is invertible in the derived category of `B'`-modules. -/
@[stacks 08QQ]
theorem mapDerived_isIso (sq : CommSq ρ α β φ)
    (h : InducesDerivedTensorQuasiIso sq) :
    IsIso (mapDerived sq) :=
  sorry

/-- A fact asserting the derived-tensor quasi-isomorphism makes the canonical
derived cotangent comparison an isomorphism. -/
instance mapDerived_isIso_of_fact (sq : CommSq ρ α β φ)
    [Fact (InducesDerivedTensorQuasiIso sq)] :
    IsIso (mapDerived sq) :=
  mapDerived_isIso sq Fact.out

end Algebra.CotangentComplex
