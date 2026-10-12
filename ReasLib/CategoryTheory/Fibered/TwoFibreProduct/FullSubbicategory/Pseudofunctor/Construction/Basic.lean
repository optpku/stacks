/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Full-subbicategory two-fibre-product pseudofunctor

The ambient composite and its canonical lift through an object property closed under the
selected pseudo-pullback.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

/-- The ambient bundled-cospan pseudofunctor underlying the selected two-fibre-product
construction. -/
private noncomputable def ambientPseudofunctor :
    Bicategory.Cospan P.FullSubbicategory ⥤ᵖ
      BasedCategory.{max v vB, max w (max u (max v vB))} C :=
  (Bicategory.Cospan.map
    (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor).comp
      (BasedCategory.PseudoPullback.pseudofunctor C)

/-- Every object in the ambient image satisfies the selected object property. -/
private theorem ambientPseudofunctor_obj_mem
    (S : Bicategory.Cospan P.FullSubbicategory) :
    P ((ambientPseudofunctor (P := P)).obj S) := sorry

variable (P) in
/-- The explicit full-subbicategory two-fibre-product construction as a pseudofunctor on
bundled cospans. -/
@[stacks 0040 "explicit two-fibre-product pseudofunctor in a full subbicategory"]
noncomputable def pseudofunctor :
    Bicategory.Cospan P.FullSubbicategory ⥤ᵖ P.FullSubbicategory :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (ambientPseudofunctor (P := P))
    (ambientPseudofunctor_obj_mem (P := P))

/- Data audit: `pseudofunctor` is a generic full-subbicategory lift of the explicit
`BasedCategory.PseudoPullback.pseudofunctor`. Its non-`Prop` fields come from the componentwise
cospan map and the ambient explicit pseudo-pullback; the closure class supplies only membership
proofs. -/

end TwoFibreProduct

end CategoryTheory
