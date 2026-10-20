/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Essential

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The canonical morphism from the target of an epimorphism `g` to the cokernel of
the composite `kernel.ι g ≫ f`. -/
def essentialEpiQuotientDesc {A B C : 𝒜} (f : A ⟶ B) (g : A ⟶ C) [Epi g] :
    C ⟶ cokernel (kernel.ι g ≫ f) :=
  Abelian.epiDesc g (f ≫ cokernel.π (kernel.ι g ≫ f)) (by
    simpa only [Category.assoc] using cokernel.condition (kernel.ι g ≫ f))

/-- Precomposing the quotient-descending morphism with `g` recovers the composite
`f ≫ cokernel.π (kernel.ι g ≫ f)`. -/
theorem comp_essentialEpiQuotientDesc {A B C : 𝒜} (f : A ⟶ B) (g : A ⟶ C) [Epi g] :
    g ≫ essentialEpiQuotientDesc f g = f ≫ cokernel.π (kernel.ι g ≫ f) := sorry

namespace Subobject.IsEssential

/-- The image of an essential subobject under an essential subobject is essential. -/
theorem trans {C : 𝒜} (B : Subobject C) (A : Subobject (B : 𝒜))
    (hA : A.IsEssential) (hB : B.IsEssential) :
    ((Subobject.map B.arrow).obj A).IsEssential := sorry

/-- Pulling an essential subobject back along any subobject arrow preserves essentiality. -/
theorem pullback {B : 𝒜} (A C : Subobject B) (hA : A.IsEssential) :
    ((Subobject.pullback C.arrow).obj A).IsEssential := sorry

end Subobject.IsEssential

namespace IsEssentialEpi

/-- The composite of two essential epimorphisms is an essential epimorphism. -/
instance comp {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}
    [IsEssentialEpi f] [IsEssentialEpi g] :
    IsEssentialEpi (f ≫ g) := sorry

end IsEssentialEpi

/-- The quotient-descending morphism associated to an essential epimorphism and an
epimorphism is an essential epimorphism. -/
instance essentialEpiQuotientDesc_isEssential {A B C : 𝒜} (f : A ⟶ B) (g : A ⟶ C)
    [Epi g] [IsEssentialEpi f] :
    IsEssentialEpi (essentialEpiQuotientDesc f g) := sorry

end CategoryTheory
