/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local equivalences and two-fibre products of groupoid-fibred categories

The chosen two-fibre-product map is functorial in a cospan transformation.  This leaf records the
site-local closure statement independently of stackification, so stack and descent layers can
reuse it without importing a chapter theorem.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace FiberedCategoryOver.Groupoids

namespace TwoFibreProduct

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

namespace map

/-- A cospan transformation whose three vertex maps are local equivalences induces a local
equivalence on the chosen two-fibre-product apices. -/
@[stacks 04Y2 "two-fibre-products preserve groupoid local equivalences"]
theorem isLocalEquivalence
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (hleft : Hom.IsLocalEquivalence J ψ.left)
    (hright : Hom.IsLocalEquivalence J ψ.right)
    (hbase : Hom.IsLocalEquivalence J ψ.base) :
    Hom.IsLocalEquivalence J (CategoryTheory.TwoFibreProduct.map ψ) := sorry

end map

end TwoFibreProduct

end FiberedCategoryOver.Groupoids

end CategoryTheory
