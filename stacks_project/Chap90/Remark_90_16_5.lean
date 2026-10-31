/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.SchlessingerH4

/-!
# Rim-Schlessinger versus Schlessinger's (H4)

When a category cofibered over `ArtinianLocalAlgCat Λ k` is cofibered in sets,
hence associated to a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`, the
Rim-Schlessinger condition (RS) is Schlessinger's condition (H4).
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/- Remark 90.16.5: when a category cofibered over `ArtinianLocalAlgCat Λ k` is
cofibered in sets, associated to a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`,
the Rim-Schlessinger condition (RS) is exactly Schlessinger's condition (H4). -/
@[stacks 06J6] #check (CategoryTheory.Functor.hasRimSchlessinger_iff_hasSchlessingerH4 :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v),
    HasRimSchlessinger (CategoryOfElements.π F) ↔ HasSchlessingerH4 F)

/- Equivalently, the induced map to the fibre product of sets is bijective. -/
#check (CategoryTheory.Functor.hasSchlessingerH4_iff :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v), HasSchlessingerH4 F ↔
    ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
      (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
      Function.Surjective f2.hom →
        Function.Bijective (pullbackObjMap_subtype F π1 π2 f1 f2 h))

end CategoryTheory.Functor
