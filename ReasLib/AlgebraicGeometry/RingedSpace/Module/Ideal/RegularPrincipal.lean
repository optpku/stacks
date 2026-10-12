/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Rank.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.SectionAction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.SectionAction.Regular
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.FiniteLimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul.Unit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally principal regular ideal sheaves

A principal chart identifies the restriction of an ideal sheaf with the structure module so that
the ideal inclusion becomes multiplication by one local section.  The corresponding property is
equivalent to finite local freeness of rank one; tensor invertibility is then supplied by the
canonical rank-one instance.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf

variable {X : RingedSpace.{u}}

/-- A principal chart for an ideal sheaf on `U` consists of a trivialization
`𝒪_X|U ≅ I|U` and a generator whose multiplication action is the ideal inclusion under that
trivialization. -/
@[stacks 0GT4 "principal chart"]
structure Chart
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (U : Opens X) where
  /-- The local trivialization, oriented from the structure module to the ideal. -/
  trivialization :
    SheafOfModules.over
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) U ≅
      SheafOfModules.over I U
  /-- The local section generating the ideal on the chart. -/
  generator : X.presheaf.obj (op U)
  /-- Under the trivialization, the ideal inclusion is multiplication by the generator. -/
  hom_comp_arrow :
    trivialization.hom ≫ (I.arrow |_ U) =
      SheafOfModules.sectionAction X.sheaf
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) U generator

namespace Chart

/-- Multiplication by the generator of a principal chart on a module sheaf. -/
@[stacks 0GT4 "principal-chart action"]
noncomputable def action
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) (M : X.Modules) :
    SheafOfModules.over M U ⟶ SheafOfModules.over M U :=
  SheafOfModules.sectionAction X.sheaf M U c.generator

/-- The chart equation in the reverse orientation: the inverse trivialization followed by
multiplication by the generator is the restricted ideal inclusion. -/
@[reassoc]
theorem inv_comp_action_eq_arrow
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) :
    c.trivialization.inv ≫
        c.action (SheafOfModules.unit X.ringCatSheaf : X.Modules) =
      I.arrow |_ U := sorry

/-- The equation needed to construct a principal chart from a trivialization oriented from the
ideal sheaf to the structure module. -/
theorem idealTrivialization_inv_comp_arrow
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X}
    (e : SheafOfModules.over I U ≅
      SheafOfModules.over
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) U)
    (s : X.presheaf.obj (op U))
    (h : e.hom ≫
      SheafOfModules.sectionAction X.sheaf
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) U s = I.arrow |_ U) :
    e.inv ≫ (I.arrow |_ U) =
      SheafOfModules.sectionAction X.sheaf
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) U s := sorry

/-- Construct a principal chart from a trivialization oriented as `I|U ≅ 𝒪_X|U`.
This is the symmetric constructor for source material using the opposite convention. -/
@[stacks 0GT4 "reverse-oriented principal chart"]
def ofIdealTrivialization
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X}
    (e : SheafOfModules.over I U ≅
      SheafOfModules.over
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) U)
    (s : X.presheaf.obj (op U))
    (h : e.hom ≫
      SheafOfModules.sectionAction X.sheaf
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) U s = I.arrow |_ U) :
    Chart I U where
  trivialization := e.symm
  generator := s
  hom_comp_arrow := idealTrivialization_inv_comp_arrow e s h

/-- The chart equation expressed through the bundled multiplication action. -/
@[reassoc]
theorem hom_comp_arrow_eq_action
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) :
    c.trivialization.hom ≫ (I.arrow |_ U) =
      c.action (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

/-- Multiplication by the generator of a principal chart is monomorphic. -/
@[stacks 0GT4 "regular principal generator", instance]
instance action_mono
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) :
    Mono (c.action (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := sorry

/-- At a point of a principal chart, the stalk ideal is generated by the germ of the chart
generator. -/
@[stacks 0GT4 "stalk ideal on a principal chart"]
theorem stalkIdeal_eq_span
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) (x : X) (hx : x ∈ U) :
    idealSheafStalkIdeal I x =
      Ideal.span {X.presheaf.germ U x hx c.generator} := sorry

/-- On a principal chart, the ideal of sections is generated by the chart generator. -/
@[stacks 0GT4 "section ideal on a principal chart"]
theorem sections_eq_span
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) :
    SheafOfModules.RingedSite.IdealSheaf.sections I (op U) =
      Ideal.span {c.generator} := sorry

/-- The generator of a principal chart belongs to the corresponding ideal of sections. -/
@[stacks 0GT4 "principal-chart generator membership"]
theorem generator_mem_sections
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) :
    c.generator ∈ SheafOfModules.RingedSite.IdealSheaf.sections I (op U) := sorry

/-- The germ of a principal-chart generator acts regularly on the stalk of the structure
module. -/
@[stacks 0GT4 "regular germ of a principal generator"]
theorem germ_isRegular
    {I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    {U : Opens X} (c : Chart I U) (x : X) (hx : x ∈ U) :
    IsSMulRegular
      (stalkModuleCat (SheafOfModules.unit X.ringCatSheaf : X.Modules) x)
      (X.presheaf.germ U x hx c.generator) := sorry

end Chart

/-- Situation 20.55.2 (0GT4): an ideal sheaf is locally principal regular when every point has
a neighborhood carrying a principal chart. -/
@[stacks 0GT4]
class IsRegularPrincipal
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)) : Prop where
  /-- A principal chart exists on a neighborhood of every point. -/
  chart (x : X) : ∃ U : Opens X, x ∈ U ∧ Nonempty (Chart I U)

namespace IsRegularPrincipal

/-- A locally principal regular ideal sheaf is finite locally free of rank one.  This canonical
fact is available to typeclass search. -/
@[stacks 0GT3 "(1), rank one", instance]
instance rankOne
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (I : X.Modules) := sorry

/-- A rank-one ideal subsheaf of the structure module is locally principal regular. -/
@[stacks 0GT3 "rank-one characterization, converse"]
theorem ofRankOne
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 (I : X.Modules)] :
    IsRegularPrincipal I := sorry

/-- Lemma 20.55.1 (0GT3) (1): a locally principal regular ideal sheaf is tensor-invertible.
The underlying instance is the canonical rank-one instance. -/
@[stacks 0GT3 "(1), invertible"]
theorem isInvertible
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] :
    CategoryTheory.MonoidalCategory.isInvertibleObject (I : X.Modules) := sorry

/-- Lemma 20.55.1 (0GT3) (2): when all structure-sheaf stalks are local rings, every
tensor-invertible ideal sheaf is locally principal regular. -/
@[stacks 0GT3 "(2)"]
theorem ofIsInvertible
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [CategoryTheory.MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsRegularPrincipal I := sorry

end IsRegularPrincipal

/-- An ideal subsheaf of the structure module is locally principal regular exactly when its
underlying module sheaf is finite locally free of rank one. -/
@[stacks 0GT3 "rank-one characterization"]
theorem isRegularPrincipal_iff_rankOne
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    IsRegularPrincipal I ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank 1 (I : X.Modules) := sorry

/-- When all structure-sheaf stalks are local rings, an ideal sheaf is locally principal regular
exactly when its underlying module sheaf is tensor-invertible. -/
@[stacks 0GT3 "equivalence"]
theorem isRegularPrincipal_iff_isInvertible
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsRegularPrincipal I ↔
      CategoryTheory.MonoidalCategory.isInvertibleObject (I : X.Modules) := sorry

end AlgebraicGeometry.RingedSpace.IdealSheaf
