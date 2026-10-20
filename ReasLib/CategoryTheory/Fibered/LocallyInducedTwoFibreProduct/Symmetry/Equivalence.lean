/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Symmetry.Swap
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Swap equivalences for locally induced two-fibre products

The ambient explicit pseudo-pullback swap equivalence is lifted through the generic locally
induced equivalence constructor. The two membership statements are the only
specialization-specific inputs.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [projections : Projections.Has (P := P) (Q := Q)]
variable [detected : Projections.IsDetected (P := P) (Q := Q)]
variable {X Y S : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)
  (fun X : P.FullSubbicategory ↦ X.1) Q}

include projections detected in
/-- The forward morphism of the ambient swap equivalence satisfies the selected hom
property. -/
theorem swap.equivalence.hom.mem (F : X ⟶ S) (G : Y ⟶ S) :
    Q (apex F G) (apex G F)
      (BasedCategory.PseudoPullback.swap.equivalence F.obj G.obj).hom := sorry

include projections detected in
/-- The inverse morphism of the ambient swap equivalence satisfies the selected hom property. -/
theorem swap.equivalence.inv.mem (F : X ⟶ S) (G : Y ⟶ S) :
    Q (apex G F) (apex F G)
      (BasedCategory.PseudoPullback.swap.equivalence F.obj G.obj).inv := sorry

/-- The canonical equivalence exchanging the two entries of a locally induced two-fibre
product. Its inverse, unit, counit, and triangle data are inherited from the ambient swap
equivalence. -/
@[stacks 02XQ "swap equivalence of locally induced two-fibre products"]
noncomputable def swap.equivalence (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ≌ apex G F :=
  Bicategory.LocallyInducedBicategory.equivalenceMk
    (BasedCategory.PseudoPullback.swap.equivalence F.obj G.obj)
    (swap.equivalence.hom.mem F G) (swap.equivalence.inv.mem F G)

section ProjectionReadout

/-- The forward morphism of the selected swap equivalence is the selected swap. -/
@[simp]
theorem swap.equivalence.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.equivalence F G).hom = swap F G := sorry

/-- The inverse morphism of the selected swap equivalence is the reverse selected swap. -/
@[simp]
theorem swap.equivalence.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.equivalence F G).inv = swap G F := sorry

/-- The unit of the locally induced swap equivalence is the ambient swap unit regarded in the
selected hom category. -/
@[simp]
theorem swap.equivalence.unit (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.equivalence F G).unit =
      (Q (apex F G) (apex F G)).isoMk
        (BasedCategory.PseudoPullback.swap.equivalence F.obj G.obj).unit := sorry

/-- The counit of the locally induced swap equivalence is the ambient swap counit regarded in the
selected hom category. -/
@[simp]
theorem swap.equivalence.counit (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.equivalence F G).counit =
      (Q (apex G F) (apex G F)).isoMk
        (BasedCategory.PseudoPullback.swap.equivalence F.obj G.obj).counit := sorry

end ProjectionReadout

/- Data audit: `swap.equivalence` retains all non-`Prop` ambient equivalence data through
`Bicategory.LocallyInducedBicategory.equivalenceMk`; only the two named membership bridges are
specialization-specific proof inputs. -/

end TwoFibreProduct
end LocallyInduced
end CategoryTheory
