/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyFiniteProduct
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Limit.CountableCoproduct
public import ReasLib.CategoryTheory.Monoidal.Invertible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally finite decompositions of derived modules on ringed sites

An invertible family consists of a locally finite product decomposition of the coefficient ring
sheaf together with an invertible module on every factor.  Restriction of scalars and shifts put
all summands in one derived category, where their coproduct is the canonical realization.
-/

@[expose] public section

-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- A locally finite family of factor ring sheaves, each equipped with an invertible module. -/
@[stacks 0FPG "invertible factor family", stacks 0FPY "invertible factor family"]
structure InvertibleFamily (O : Sheaf J CommRingCat.{max u v}) where
  /-- The locally finite product decomposition of the coefficient ring sheaf. -/
  rings : CategoryTheory.Sheaf.LocallyFiniteProduct O ℤ
  /-- The invertible module carried by the factor in degree `n`. -/
  summand (n : ℤ) : ringedSiteModuleCategory J (rings.factor n)
  /-- Every factor module is tensor-invertible over its own factor ring sheaf. -/
  invertible (n : ℤ) : isInvertibleObject (summand n)

namespace InvertibleFamily

/-- The invertibility witness stored by an invertible family is available to typeclass search. -/
instance summand_isInvertible (F : InvertibleFamily O) (n : ℤ) :
    isInvertibleObject (F.summand n) :=
  F.invertible n

/-- A factor module viewed as a module over the original product ring sheaf by restriction of
scalars along the corresponding product projection. -/
noncomputable def restrictedSummand (F : InvertibleFamily O) (n : ℤ) :
    ringedSiteModuleCategory J O :=
  (restrictionAlong (F.rings.π n)).obj (F.summand n)

/-- The derived summand contributed by degree `n`, placed cohomologically in that degree. -/
@[stacks 0FPG "shifted factor term", stacks 0FPY "shifted factor term"]
noncomputable def term (F : InvertibleFamily O) (n : ℤ) :
    RingedSite.Hom.ModuleDerived.{max u v} (RingedSite.ofCommRingSheaf J O) :=
  ((DerivedCategory.singleFunctor (ringedSiteModuleCategory J O) (0 : ℤ)).obj
    (F.restrictedSummand n))⟦-n⟧

/-- The canonical derived realization of an invertible family as the coproduct of its shifted
factor terms. -/
@[stacks 0FPG "realization of an invertible factor family",
  stacks 0FPY "realization of an invertible factor family"]
noncomputable def realization (F : InvertibleFamily O) :
    RingedSite.Hom.ModuleDerived.{max u v} (RingedSite.ofCommRingSheaf J O) :=
  ∐ fun n : ℤ ↦ F.term n

end InvertibleFamily

/-- A specified locally finite invertible decomposition of a derived module. -/
@[stacks 0FPG "invertible decomposition", stacks 0FPY "invertible decomposition"]
structure InvertibleDecomposition
    (M : RingedSite.Hom.ModuleDerived.{max u v} (RingedSite.ofCommRingSheaf J O)) where
  /-- The family of ring factors and invertible module summands. -/
  family : InvertibleFamily O
  /-- The specified identification with the realization of the factor family. -/
  iso : M ≅ family.realization

/-- A derived module admits an invertible decomposition when such decomposition data are
nonempty. -/
@[stacks 0FPG "existence of an invertible decomposition",
  stacks 0FPY "existence of an invertible decomposition"]
abbrev HasInvertibleDecomposition
    (M : RingedSite.Hom.ModuleDerived.{max u v} (RingedSite.ofCommRingSheaf J O)) : Prop :=
  Nonempty (InvertibleDecomposition M)

/-- Existence of an invertible decomposition is exactly the existence of an invertible family
whose realization is isomorphic to the given derived module. -/
theorem hasInvertibleDecomposition_iff
    (M : RingedSite.Hom.ModuleDerived.{max u v} (RingedSite.ofCommRingSheaf J O)) :
    HasInvertibleDecomposition M ↔
      ∃ F : InvertibleFamily O, Nonempty (M ≅ F.realization) := sorry

section Characterization

variable [RingedSite.Hom.ModuleDerived.KFlat.HomotopyTensorDescends
  (C := C) (J := J) O]
variable [RingedSite.Hom.ModuleDerived.KFlat.TensorDescends
  (C := C) (J := J) O]
variable [RingedSite.Hom.ModuleDerived.KFlat.IsLocalization
  (C := C) (J := J) O]

/-- Lemma 21.49.2 (1): a derived module sheaf is tensor-invertible exactly when it admits a
locally finite invertible decomposition. -/
@[stacks 0FPY "(1)"]
theorem isInvertible_iff_hasDecomposition
    (M : RingedSite.Hom.ModuleDerived.{max u v}
      (RingedSite.ofCommRingSheaf J O)) :
    isInvertibleObject M ↔ HasInvertibleDecomposition M := sorry

end Characterization

end SheafOfModules.RingedSite
