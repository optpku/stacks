/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Closure
public import ReasLib.CategoryTheory.Sites.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closure of quasi-coherent derived modules on a chaotic site

The canonical section and restriction comparisons make `Chaotic.QC` a triangulated full
subcategory closed under arbitrary coproducts.  Mathlib's full-subcategory instances derive the
corresponding zero, shift, triangulated, and colimit structures from these two property owners.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open SheafOfModules.RingedSite

universe t u v w

namespace CategoryTheory.ModulesOnCategory.Chaotic

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]

/-- Coproducts indexed in the coefficient universe are exact for module sheaves on a chaotic
site because they are computed objectwise. -/
@[stacks 0GYW "exact coproducts on the chaotic module category",
  stacks 0GZ0 "(1), arbitrary coproducts"]
theorem ambientHasExactCoproducts
    (I : Type (max (max u v) w)) :
    HasExactColimitsOfShape (Discrete I)
      (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
        (⊥ : GrothendieckTopology C) 𝒪) := sorry

/-- The ambient derived category has all coproducts indexed in the coefficient universe. -/
@[stacks 0GYW "coproducts in the ambient derived category",
  stacks 0GZ0 "(1), ambient arbitrary coproducts"]
theorem ambientDerivedHasCoproducts :
    HasCoproducts.{max (max u v) w}
      (RingedSite.Hom.ModuleDerived.{max (max u v) w}
        (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪)) := sorry

/-- Canonical quasi-coherence on the chaotic site is a triangulated object property. -/
@[stacks 0GYW "triangulated canonical quasi-coherence", stacks 0GZ0 "(1), triangulated"]
instance isTriangulated : ObjectProperty.IsTriangulated (isQuasiCoherent 𝒪) := sorry

/-- Canonical quasi-coherence on the chaotic site is closed under `I`-indexed coproducts. -/
@[stacks 0GYW "arbitrary coproducts", stacks 0GZ0 "(1), arbitrary coproducts"]
instance isClosedUnderCoproducts (I : Type t) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (isQuasiCoherent 𝒪) (Discrete I) := sorry

/-- The canonical quasi-coherent derived category has all coproducts indexed in the coefficient
universe. -/
@[stacks 0GYW "coproducts in canonical quasi-coherence",
  stacks 0GZ0 "(1), quasi-coherent arbitrary coproducts"]
instance hasCoproducts : HasCoproducts.{max (max u v) w} (QC 𝒪) := sorry

end CategoryTheory.ModulesOnCategory.Chaotic
