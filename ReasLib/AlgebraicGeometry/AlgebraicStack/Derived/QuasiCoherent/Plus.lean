/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open DerivedCategory DerivedCategory.TStructure
open scoped Bicategory

noncomputable section

universe u

-- Local instance justification (defeq pin): the homotopy localization must use the Abelian and induced additive structures of the fppf module presentation in ModuleDerived.
attribute [local instance 2000] GroupoidsOver.fppfModulesAbelian
  Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms fppfModulesHasDerivedCategory

-- Local instance justification (defeq pin): ModuleDerived uses this standard localization through fppfModulesHasDerivedCategory, at the same module-category universe.
attribute [local instance 1900] HasDerivedCategory.standard



namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Bounded-below derived objects of fppf `𝒪_X`-modules with cohomology in
`LQCoh^{fbc}(𝒪_X)`. -/
abbrev DerivedLQCohFbc.Plus (X : GroupoidsOver S) [AlgebraicStack X] :=
  Plus.CohomologyIn (FppfModules.lqcohFbc X)

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.Plus

variable {S : Scheme.{u}}

/-- The inclusion of `D⁺_{LQCoh^{fbc}}(𝒪_X)` into bounded-below `D⁺(𝒪_X)`. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc.Plus X ⥤ DerivedCategory.Plus (fppfModules X) :=
  (DerivedCategory.Plus.cohomologyIn (FppfModules.lqcohFbc X)).ι

/-- The inclusion of `D⁺_{LQCoh^{fbc}}(𝒪_X)` into unbounded
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
abbrev toUnbounded (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc.Plus X ⥤ DerivedLQCohFbc X :=
  Plus.CohomologyIn.toUnbounded (FppfModules.lqcohFbc X)

/-- The inclusion of `D⁺_{LQCoh^{fbc}}(𝒪_X)` into unbounded `D(𝒪_X)`. -/
abbrev ambient (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc.Plus X ⥤ ModuleDerived X :=
  Plus.CohomologyIn.ambient (FppfModules.lqcohFbc X)

/-- `toUnbounded` commutes with shifts. -/
instance toUnbounded.instCommShift (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (toUnbounded X).CommShift ℤ :=
  inferInstanceAs (((DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).lift
    ((DerivedCategory.Plus.cohomologyIn (FppfModules.lqcohFbc X)).ι ⋙ DerivedCategory.Plus.ι)
    (fun E => E.property)).CommShift ℤ)

/-- `toUnbounded` is a triangulated functor. -/
instance toUnbounded.instIsTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (toUnbounded X).IsTriangulated := sorry

end AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.Plus

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Bounded-below derived objects of fppf `𝒪_X`-modules with cohomology in
`Parasitic ∩ LQCoh^{fbc}`. -/
abbrev derivedParasiticLQCohFbcPlus (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  Plus.CohomologyIn (FppfModules.parasiticLQCohFbc X)

/-- The inclusion of `D⁺_{Parasitic ∩ LQCoh^{fbc}}` into
`D⁺_{LQCoh^{fbc}}`. -/
abbrev derivedParasiticLQCohFbcPlus.inclusion (X : GroupoidsOver S)
    [AlgebraicStack X] :
    derivedParasiticLQCohFbcPlus X ⥤ DerivedLQCohFbc.Plus X :=
  Plus.CohomologyIn.inclusion ((inf_le_right : FppfModules.parasiticLQCohFbc X ≤ FppfModules.lqcohFbc X))

/-- The property of an object of `D⁺_{LQCoh^{fbc}}(𝒪_X)` having parasitic
cohomology sheaves. -/
abbrev derivedParasiticPlus (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (DerivedLQCohFbc.Plus X) :=
  (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X)).inverseImage
    (DerivedLQCohFbc.Plus.inclusion X)

/-- An object of `D⁺_{LQCoh^{fbc}}(𝒪_X)` lies in `derivedParasiticPlus X` iff
every cohomology sheaf is a parasitic object of fppf `LQCoh^{fbc}`. -/
theorem derivedParasiticPlus_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (E : DerivedLQCohFbc.Plus X) :
    derivedParasiticPlus X E ↔
      ∀ n : ℤ, FppfModules.parasiticLQCohFbc X
        ((Plus.homologyFunctor (fppfModules X) n).obj
          ((DerivedLQCohFbc.Plus.inclusion X).obj E)) := sorry

/-- Objects of `D⁺_{LQCoh^{fbc}}(𝒪_X)` with parasitic cohomology form a
triangulated subcategory. -/
instance derivedParasiticPlus_isTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasiticPlus X).IsTriangulated := sorry

/-- The bounded-below derived category of `𝒪_X`-modules with quasi-coherent
cohomology, as the Verdier quotient of `D⁺_{LQCoh^{fbc}}(𝒪_X)` by objects with
parasitic cohomology. -/
abbrev DerivedQCoh.Plus (X : GroupoidsOver S) [AlgebraicStack X] :=
  verdierQuotient (derivedParasiticPlus X)

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.DerivedQCoh.Plus

variable {S : Scheme.{u}}

/-- The canonical functor from `D⁺_{LQCoh^{fbc}}(𝒪_X)` to the Verdier quotient
`D⁺_QCoh(𝒪_X)`. -/
abbrev quotientFunctor (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc.Plus X ⥤ DerivedQCoh.Plus X :=
  verdierQuotientFunctor (derivedParasiticPlus X)

/-- The composite of bounded-below `toUnbounded` with the unbounded Verdier
quotient functor `DerivedQCoh.quotientFunctor`. -/
abbrev toUnboundedComposite (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc.Plus X ⥤ DerivedQCoh X :=
  DerivedLQCohFbc.Plus.toUnbounded X ⋙ DerivedQCoh.quotientFunctor X

/-- `toUnbounded` sends objects with parasitic plus cohomology into the
unbounded parasitic subcategory. -/
theorem toUnbounded_maps_parasitic (X : GroupoidsOver S)
    [AlgebraicStack X] :
    derivedParasiticPlus X ≤
      (derivedParasitic X).inverseImage
        (DerivedLQCohFbc.Plus.toUnbounded X) := sorry

/-- The composite through unbounded `DerivedQCoh` inverts the plus parasitic
Verdier system. -/
theorem toUnboundedComposite_inverts (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasiticPlus X).trW.IsInvertedBy (toUnboundedComposite X) := sorry

/-- The composite `toUnboundedComposite` commutes with shifts. -/
instance toUnboundedComposite.instCommShift (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (toUnboundedComposite X).CommShift ℤ := inferInstance

/-- The composite `toUnboundedComposite` is triangulated. -/
instance toUnboundedComposite.instIsTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (toUnboundedComposite X).IsTriangulated := sorry

/-- Comparison from `D⁺_QCoh(𝒪_X)` to unbounded `D_QCoh(𝒪_X)`. -/
def inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCoh.Plus X ⥤ DerivedQCoh X :=
  VerdierQuotient.Exact.factor (derivedParasiticPlus X)
    (toUnboundedComposite X) (toUnboundedComposite_inverts X)

/-- Canonical comparison from the plus quotient functor followed by
`inclusion` to `toUnboundedComposite`. -/
abbrev inclusion_facIso (X : GroupoidsOver S) [AlgebraicStack X] :
    quotientFunctor X ⋙ inclusion X ≅ toUnboundedComposite X :=
  VerdierQuotient.Exact.factor.facIso (derivedParasiticPlus X)
    (toUnboundedComposite X) (toUnboundedComposite_inverts X)

/-- Strict factorization of `inclusion` through `quotientFunctor`. -/
theorem inclusion_fac (X : GroupoidsOver S) [AlgebraicStack X] :
    quotientFunctor X ⋙ inclusion X = toUnboundedComposite X := sorry

/-- `DerivedQCoh.Plus.inclusion` commutes with shifts. -/
instance inclusion.instCommShift (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (inclusion X).CommShift ℤ :=
  VerdierQuotient.Exact.factor.commShift (derivedParasiticPlus X)
    (toUnboundedComposite X) (toUnboundedComposite_inverts X)

/-- `DerivedQCoh.Plus.inclusion` is triangulated. -/
instance inclusion.instIsTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    @Functor.IsTriangulated _ _ _ _ _ _ (inclusion X) inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus X) n)
      (fun n => VerdierQuotient.shiftAdditive (derivedParasitic X) n)
      inferInstance inferInstance :=
  VerdierQuotient.Exact.factor.isTriangulated (derivedParasiticPlus X)
    (toUnboundedComposite X) (toUnboundedComposite_inverts X)

end AlgebraicGeometry.AlgebraicStack.DerivedQCoh.Plus
