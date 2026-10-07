module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Biterminal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Biterminal
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Bilimit

/-!
# Two-fibre-product cones in the pith of fibred categories

The generic locally induced cone descends to the pith of fibred categories, retaining only
invertible vertical `2`-morphisms.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct
namespace Pith

variable {X Y S : Bicategory.Pith
  (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}

/-- The two-fibre-product cone in the pith of fibred categories. It has the same
objects and `1`-morphisms as
`LocallyInduced.TwoFibreProduct.cone (P := BasedCategory.isFibered C)
  (Q := FiberedCategoryOver.homProperty C) F.of G.of`,
while only invertible vertical `2`-morphisms are retained. -/
@[stacks 02XQ "locally induced two-fibre-product cone"]
noncomputable def cone
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G :=
  Bicategory.PseudoPullbackCone.toPith
    (LocallyInduced.TwoFibreProduct.cone
      (P := BasedCategory.isFibered C) (Q := FiberedCategoryOver.homProperty C) F.of G.of)

namespace cone

/-- The apex of the pith two-fibre-product cone is the explicit locally induced apex. -/
@[simp]
theorem pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt =
      Bicategory.Pith.mk
        (LocallyInduced.TwoFibreProduct.apex
          (P := BasedCategory.isFibered C) (Q := FiberedCategoryOver.homProperty C) F.of G.of) := sorry

/-- The first leg of the pith two-fibre-product cone is the retained first projection. -/
@[simp]
theorem fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst =
      Core.mk
        (LocallyInduced.TwoFibreProduct.fst
          (P := BasedCategory.isFibered C) (Q := FiberedCategoryOver.homProperty C) F.of G.of) := sorry

/-- The second leg of the pith two-fibre-product cone is the retained second projection. -/
@[simp]
theorem snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd =
      Core.mk
        (LocallyInduced.TwoFibreProduct.snd
          (P := BasedCategory.isFibered C) (Q := FiberedCategoryOver.homProperty C) F.of G.of) := sorry

/-- The structural cell of the pith two-fibre-product cone is the retained comparison
isomorphism. -/
@[simp]
theorem iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso =
      Core.isoMk
        (LocallyInduced.TwoFibreProduct.comparisonIso
          (P := BasedCategory.isFibered C) (Q := FiberedCategoryOver.homProperty C) F.of G.of) := sorry

/-- The explicit pseudo-pullback cone is biterminal in the pith of fibred categories over the
fixed base. -/
@[stacks 02XQ]
theorem isBiterminal
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsBiterminal (cone F G) := sorry
/- Proof strategy: apply `PseudoPullbackCone.isBiterminal_of_isBilimit`; the full cone is a
bilimit by `LocallyInduced.TwoFibreProduct.cone.isBilimit`, and
`PseudoPullbackCone.toPith.isBilimit` restricts its comparison equivalences to the pith. -/

end cone

end Pith
end TwoFibreProduct
end LocallyInduced

end CategoryTheory
