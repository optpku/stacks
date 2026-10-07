module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf

/-!
# Canonical sections of differences of effective Cartier divisors

The canonical section of the positive divisor induces a morphism from the
negative-divisor sheaf to the corresponding difference sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Tensoring the canonical section of `D` with the identity on `𝒪(-E)` gives
the canonical morphism `𝒪(-E) ⟶ 𝒪(D - E)`. -/
noncomputable def differenceCanonicalSectionHom
    (D E : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [AlgebraicGeometry.IsEffectiveCartierDivisor E.subschemeι] :
    E.negSheaf ⟶ D.differenceSheaf E :=
  (λ_ E.negSheaf).inv ≫
    tensorHom
      (SheafOfModules.RingedSite.unitIsoTensorUnit
        (J := Opens.grothendieckTopology X.toTopCat)
        (𝒪 := X.𝒪)).inv
      (𝟙 E.negSheaf) ≫
    tensorHom
      (D.associatedSheaf.unitHomEquiv.symm D.canonicalSection)
      (𝟙 E.negSheaf)

end AlgebraicGeometry.Scheme.IdealSheafData
