/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc

/-!
# Derived category of quasi-coherent modules on an algebraic stack

For an algebraic stack `X`, `DerivedQCoh X` is the Verdier quotient of
`D_{LQCoh^{fbc}}(𝒪_X)` by the triangulated subcategory of objects with
parasitic cohomology, formed inside `D(𝒪_X) = D(Mod(X_fppf, 𝒪_X))`. This is
not the full subcategory of `D(𝒪_X)` on quasi-coherent cohomology, because
`QCoh(𝒪_X) → Mod(𝒪_X)` is not exact. The analogous étale quotient is
`DerivedQCohEtale`, compared later by `ε^*`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The standard derived-category structure on fppf `𝒪_X`-modules on an
algebraic stack. -/
instance fppfModulesHasDerivedCategory {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (fppfModules X) :=
  HasDerivedCategory.standard (fppfModules X)

/-- The unbounded derived category `D(𝒪_X)` of fppf module sheaves on an
algebraic stack. -/
abbrev ModuleDerived {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  DerivedCategory (fppfModules X)

/-- `ModuleDerived X` is the derived category of fppf `𝒪_X`-modules. -/
theorem ModuleDerived_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    ModuleDerived X = DerivedCategory (fppfModules X) := sorry

/-- The derived category of fppf `𝒪_X`-modules with cohomology in
`LQCoh^{fbc}(𝒪_X)`. -/
abbrev DerivedLQCohFbc {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  DerivedCategory.CohomologyIn (FppfModules.lqcohFbc X)

/-- The cohomology-in property of fppf `lqcohFbc` is a triangulated subcategory
of `D(𝒪_X)`. -/
instance derivedLQCohFbc_isTriangulated {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).IsTriangulated :=
  sorry

namespace DerivedLQCohFbc

/-- The inclusion of `D_{LQCoh^{fbc}}(𝒪_X)` into `D(𝒪_X)`. -/
abbrev inclusion {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc X ⥤ ModuleDerived X :=
  (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).ι

/-- An object of `D(𝒪_X)` lies in `DerivedLQCohFbc X` iff every cohomology
sheaf lies in fppf `LQCoh^{fbc}(𝒪_X)`. -/
theorem mem_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (E : ModuleDerived X) :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) E ↔
      ∀ n : ℤ, FppfModules.lqcohFbc X
        ((DerivedCategory.homologyFunctor (fppfModules X) n).obj E) := sorry

end DerivedLQCohFbc

/-- The property of an object of `D_{LQCoh^{fbc}}(𝒪_X)` having parasitic
cohomology sheaves. -/
abbrev derivedParasitic {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    ObjectProperty (DerivedLQCohFbc X) :=
  (DerivedCategory.cohomologyIn (FppfModules.parasitic X)).inverseImage
    (DerivedLQCohFbc.inclusion X)

/-- An object of `D_{LQCoh^{fbc}}(𝒪_X)` lies in `derivedParasitic X` iff every
cohomology sheaf is a parasitic fppf module. -/
theorem derivedParasitic_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (E : DerivedLQCohFbc X) :
    derivedParasitic X E ↔
      ∀ n : ℤ, FppfModules.parasitic X
        ((DerivedCategory.homologyFunctor (fppfModules X) n).obj
          ((DerivedLQCohFbc.inclusion X).obj E)) := sorry

/-- The parasitic cohomology property on `D_{LQCoh^{fbc}}` is the cohomology-in
property of `Parasitic ∩ LQCoh^{fbc}`, pulled back along the inclusion. -/
theorem derivedParasitic_eq_intersection {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    derivedParasitic X =
      (DerivedCategory.cohomologyIn (FppfModules.parasiticLQCohFbc X)).inverseImage
        (DerivedLQCohFbc.inclusion X) := sorry

/-- Objects of `D_{LQCoh^{fbc}}(𝒪_X)` with parasitic cohomology form a
triangulated subcategory. -/
instance derivedParasitic_isTriangulated {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasitic X).IsTriangulated := sorry

/-- The derived category of `𝒪_X`-modules with quasi-coherent cohomology
sheaves, as the Verdier quotient of `D_{LQCoh^{fbc}}(𝒪_X)` by the subcategory
of objects with parasitic cohomology, formed in `D(Mod(X_fppf, 𝒪_X))`. -/
abbrev DerivedQCoh {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  ObjectProperty.verdierQuotient (derivedParasitic X)

namespace DerivedQCoh

/-- The canonical functor from `D_{LQCoh^{fbc}}(𝒪_X)` to the Verdier quotient
`D_QCoh(𝒪_X)`. -/
abbrev quotientFunctor {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedLQCohFbc X ⥤ DerivedQCoh X :=
  ObjectProperty.verdierQuotientFunctor (derivedParasitic X)

/-- `DerivedQCoh X` is the Verdier quotient by `derivedParasitic X`. -/
theorem eq {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCoh X = ObjectProperty.verdierQuotient (derivedParasitic X) :=
  sorry

/-- Source-semantic unfolding: `D_QCoh(𝒪_X)` is the Verdier quotient of
`D_{LQCoh^{fbc}}(𝒪_X)` by `D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)` inside
`D(Mod(X_fppf, 𝒪_X))`. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCoh X =
      ObjectProperty.verdierQuotient
        ((DerivedCategory.cohomologyIn
            (FppfModules.parasiticLQCohFbc X)).inverseImage
          (DerivedLQCohFbc.inclusion X)) := sorry

end DerivedQCoh

/-- The standard derived-category structure on étale `𝒪_X`-modules. -/
instance etaleModulesHasDerivedCategory {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (etaleModules X) :=
  HasDerivedCategory.standard (etaleModules X)

/-- The unbounded derived category of étale module sheaves, used in the étale
comparison of lemma 07B8. -/
abbrev ModuleDerivedEtale {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  DerivedCategory (etaleModules X)

/-- The derived category of étale `𝒪_X`-modules with cohomology in étale
`LQCoh^{fbc}`. -/
abbrev DerivedLQCohFbcEtale {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  DerivedCategory.CohomologyIn (lqcohFbc X)

/-- The inclusion of the étale cohomology-in subcategory into étale
`D(𝒪_X)`. -/
abbrev DerivedLQCohFbcEtale.inclusion {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedLQCohFbcEtale X ⥤ ModuleDerivedEtale X :=
  (DerivedCategory.cohomologyIn (lqcohFbc X)).ι

/-- The property of an étale `D_{LQCoh^{fbc}}` object having parasitic
cohomology. -/
abbrev derivedParasiticEtale {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    ObjectProperty (DerivedLQCohFbcEtale X) :=
  (DerivedCategory.cohomologyIn (EtaleModules.parasitic X)).inverseImage
    (DerivedLQCohFbcEtale.inclusion X)

/-- The étale Verdier quotient compared with `DerivedQCoh` by lemma 07B8. -/
abbrev DerivedQCohEtale {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  ObjectProperty.verdierQuotient (derivedParasiticEtale X)

/-- `DerivedQCohEtale X` is the étale Verdier quotient by parasitic
cohomology. -/
theorem DerivedQCohEtale_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohEtale X =
      ObjectProperty.verdierQuotient (derivedParasiticEtale X) := sorry

end AlgebraicGeometry.AlgebraicStack
