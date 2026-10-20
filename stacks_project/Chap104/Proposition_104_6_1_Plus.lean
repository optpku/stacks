module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Exact
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Bounded-below derived categories of quasi-coherent modules on algebraic stacks

`DerivedLQCohFbc.Plus` is `D⁺_{LQCoh^{fbc}}(𝒪_X)`, and `DerivedQCoh.Plus` is the
Verdier quotient of that category by objects with parasitic cohomology. This is
the quotient of plus categories, not the plus subcategory of unbounded
`DerivedQCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The coefficient inclusion `Parasitic ∩ LQCoh^{fbc} ≤ LQCoh^{fbc}` of fppf
modules. -/
theorem FppfModules.parasiticLQCohFbc_le_lqcohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] :
    FppfModules.parasiticLQCohFbc X ≤ FppfModules.lqcohFbc X := sorry

/-- Bounded-below derived objects of fppf `𝒪_X`-modules with cohomology in
`LQCoh^{fbc}(𝒪_X)`. -/
abbrev DerivedLQCohFbc.Plus (X : GroupoidsOver S) [AlgebraicStack X] :=
  Plus.CohomologyIn (FppfModules.lqcohFbc X)

namespace DerivedLQCohFbc.Plus

/-- `DerivedLQCohFbc.Plus X` is the bounded-below cohomology-in subcategory of
fppf `lqcohFbc`. -/
theorem eq (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc.Plus X =
      Plus.CohomologyIn (FppfModules.lqcohFbc X) := sorry

/-- An object of `D⁺(𝒪_X)` lies in `DerivedLQCohFbc.Plus X` iff every
cohomology sheaf lies in fppf `LQCoh^{fbc}(𝒪_X)`. -/
theorem mem_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (E : DerivedCategory.Plus (fppfModules X)) :
    DerivedCategory.Plus.cohomologyIn (FppfModules.lqcohFbc X) E ↔
      ∀ n : ℤ, FppfModules.lqcohFbc X
        ((DerivedCategory.Plus.homologyFunctor (fppfModules X) n).obj E) := sorry

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

/-- `ambient` is the composite of the plus-subcategory inclusion with
`Plus.ι`. -/
theorem ambient_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    ambient X = inclusion X ⋙ DerivedCategory.Plus.ι := sorry

/-- Bounded-below cohomology-in objects of fppf `lqcohFbc` form a triangulated
subcategory of `D⁺(𝒪_X)`. -/
instance cohomologyIn_isTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (Plus.cohomologyIn (FppfModules.lqcohFbc X)).IsTriangulated :=
  inferInstance

/-- `toUnbounded` commutes with shifts. -/
instance toUnbounded.instCommShift (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (toUnbounded X).CommShift ℤ :=
  Functor.CommShift.ofComp (Plus.CohomologyIn.toUnbounded.compιIso
    (FppfModules.lqcohFbc X)) ℤ

/-- `toUnbounded` is a triangulated functor. -/
instance toUnbounded.instIsTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (toUnbounded X).IsTriangulated := sorry

end DerivedLQCohFbc.Plus

/-- Bounded-below derived objects of fppf `𝒪_X`-modules with cohomology in
`Parasitic ∩ LQCoh^{fbc}`. -/
abbrev derivedParasiticLQCohFbcPlus (X : GroupoidsOver S)
    [AlgebraicStack X] :=
  Plus.CohomologyIn (FppfModules.parasiticLQCohFbc X)

/-- `derivedParasiticLQCohFbcPlus X` is the bounded-below cohomology-in
subcategory of fppf `parasiticLQCohFbc`. -/
theorem derivedParasiticLQCohFbcPlus_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    derivedParasiticLQCohFbcPlus X =
      Plus.CohomologyIn (FppfModules.parasiticLQCohFbc X) := sorry

/-- An object of `D⁺(𝒪_X)` lies in `derivedParasiticLQCohFbcPlus X` iff every
cohomology sheaf is parasitic and lies in fppf `LQCoh^{fbc}`. -/
theorem derivedParasiticLQCohFbcPlus_mem_iff {X : GroupoidsOver S}
    [AlgebraicStack X] (E : Plus (fppfModules X)) :
    Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X) E ↔
      ∀ n : ℤ, FppfModules.parasiticLQCohFbc X
        ((Plus.homologyFunctor (fppfModules X) n).obj E) := sorry

/-- The inclusion of `D⁺_{Parasitic ∩ LQCoh^{fbc}}` into
`D⁺_{LQCoh^{fbc}}`. -/
abbrev derivedParasiticLQCohFbcPlus.inclusion (X : GroupoidsOver S)
    [AlgebraicStack X] :
    derivedParasiticLQCohFbcPlus X ⥤ DerivedLQCohFbc.Plus X :=
  Plus.CohomologyIn.inclusion (FppfModules.parasiticLQCohFbc_le_lqcohFbc X)

/-- Bounded-below cohomology-in objects of fppf `parasiticLQCohFbc` form a
triangulated subcategory of `D⁺(𝒪_X)`. -/
instance derivedParasiticLQCohFbcPlus_cohomologyIn_isTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X)).IsTriangulated :=
  inferInstance

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

namespace DerivedQCoh.Plus

/-- `DerivedQCoh.Plus X` is the Verdier quotient of `DerivedLQCohFbc.Plus X` by
`derivedParasiticPlus X`. -/
theorem eq (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCoh.Plus X = verdierQuotient (derivedParasiticPlus X) := sorry

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

/-- `toUnboundedComposite` is `toUnbounded` followed by the unbounded quotient
functor. -/
theorem toUnboundedComposite_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    toUnboundedComposite X =
      DerivedLQCohFbc.Plus.toUnbounded X ⋙ DerivedQCoh.quotientFunctor X :=
  sorry

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
    (derivedParasiticPlus X).trW.IsInvertedBy (toUnboundedComposite X) :=
  sorry

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

/-- `inclusion` is the exact Verdier factor of `toUnboundedComposite`. -/
theorem inclusion_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    inclusion X =
      VerdierQuotient.Exact.factor (derivedParasiticPlus X)
        (toUnboundedComposite X) (toUnboundedComposite_inverts X) := sorry

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
    (inclusion X).IsTriangulated :=
  VerdierQuotient.Exact.factor.isTriangulated (derivedParasiticPlus X)
    (toUnboundedComposite X) (toUnboundedComposite_inverts X)

end DerivedQCoh.Plus

end AlgebraicGeometry.AlgebraicStack
