/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.Cokernel
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat cokernels from Tor-amplitude

For a bounded-above termwise-flat representative, a lower Tor-amplitude bound forces the
boundary cokernel at that bound to be flat.  The primary theorem consumes the derived-category
Tor predicate; a separate exactness formulation is retained for proof construction.
-/

@[expose] public section

-- Infer the existing canonical tensor model for this commutative presentation.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
  SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite.Hom

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

namespace FlatCokernel

/-- Exactness of tensoring a termwise-flat representative at degree `a - 1` makes its
canonical opcycles object in degree `a` flat. -/
theorem ofExactAtTensorSingle
    (E : CochainComplex (ringedSiteModuleCategory J O) ℤ) (a : ℤ)
    (hFlat : HomologicalComplex.IsTermwiseFlat E)
    (hExact : ∀ M : ringedSiteModuleCategory J O,
      (HomologicalComplex.tensorObj E
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory J O) 0).obj M)).ExactAt
          (a - 1)) :
    IsFlat O (E.opcycles a) := sorry

/-- A bounded-above termwise-flat representative of an object with lower Tor-amplitude bound
`a` has flat opcycles in degree `a`. -/
@[stacks 08G0 "lower-bound opcycles form"]
theorem ofTorAmplitudeGE
    (E : CochainComplex
      (_root_.RingedSite.ModuleCat.{w} (_root_.RingedSite.ofCommRingSheaf J O)) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ringedSiteModuleCategory J O) E)
    (hFlat : HomologicalComplex.IsTermwiseFlat E)
    (hTor : ModuleDerived.HasTorAmplitudeGE
      (X := _root_.RingedSite.ofCommRingSheaf J O) (DerivedCategory.Q.obj E) a) :
    IsFlat O (E.opcycles a) := sorry

/-- A bounded-above termwise-flat representative of an object with Tor-amplitude in `[a, b]`
has flat cokernel at the differential leaving degree `a - 1`. -/
@[stacks 08G0]
theorem ofTorAmplitudeIn
    (E : CochainComplex
      (_root_.RingedSite.ModuleCat.{w} (_root_.RingedSite.ofCommRingSheaf J O)) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ringedSiteModuleCategory J O) E)
    (hFlat : HomologicalComplex.IsTermwiseFlat E)
    (hTor : ModuleDerived.HasTorAmplitudeIn
      (X := _root_.RingedSite.ofCommRingSheaf J O) (DerivedCategory.Q.obj E) a b) :
    IsFlat O (cokernel (E.dFrom (a - 1))) := sorry

end FlatCokernel

end SheafOfModules.RingedSite
