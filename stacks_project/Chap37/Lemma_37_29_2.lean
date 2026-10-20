/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent.BaseChange

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace Section

/- Lemma 37.29.2: the component locus selected by a section is preserved by
base change, as the inverse image along the induced morphism. -/
@[stacks 055M] #check
  (AlgebraicGeometry.Scheme.Hom.Section.componentLocus_baseChange :
    ∀ {X Y X' Y' : Scheme.{u}}
      (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
      (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (hcart : IsPullback g' f' f g) (s' : Y' ⟶ X')
      (hs' : s' ≫ f' = 𝟙 Y') (hs_baseChange : s' ≫ g' = g ≫ s),
      componentLocus f' s' hs' = g' ⁻¹' componentLocus f s hs)

end Section
end Hom
end Scheme
end AlgebraicGeometry
