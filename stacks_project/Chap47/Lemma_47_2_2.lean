/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Abelian.Essential.Closure
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Lemma 47.2.2 (1): If `A` is an essential subobject of `B` and `B` is an essential
subobject of `C`, then the composite subobject `A ⊆ C` is essential. -/
@[stacks 08XK] #check (CategoryTheory.Subobject.IsEssential.trans :
  ∀ {C : 𝒜} (B : Subobject C) (A : Subobject (B : 𝒜)),
    A.IsEssential → B.IsEssential → ((Subobject.map B.arrow).obj A).IsEssential)

/- Lemma 47.2.2 (2): If `A` is an essential subobject of `B`, then its intersection
with any subobject `C` is essential as a subobject of `C`. -/
@[stacks 08XK] #check (CategoryTheory.Subobject.IsEssential.pullback :
  ∀ {B : 𝒜} (A C : Subobject B),
    A.IsEssential → ((Subobject.pullback C.arrow).obj A).IsEssential)

/- Lemma 47.2.2 (3): The composite of two essential epimorphisms is essential. -/
@[stacks 08XK] #check (CategoryTheory.IsEssentialEpi.comp :
  ∀ {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}
    [IsEssentialEpi f] [IsEssentialEpi g], IsEssentialEpi (f ≫ g))

/- Lemma 47.2.2 (4): If `f : A ⟶ B` is an essential epimorphism and `g : A ⟶ C`
is an epimorphism, then the induced map `C ⟶ cokernel (kernel.ι g ≫ f)` is essential. -/
@[stacks 08XK] #check (CategoryTheory.essentialEpiQuotientDesc_isEssential :
  ∀ {A B C : 𝒜} (f : A ⟶ B) (g : A ⟶ C) [Epi g] [IsEssentialEpi f],
    IsEssentialEpi (CategoryTheory.essentialEpiQuotientDesc f g))

end CategoryTheory
