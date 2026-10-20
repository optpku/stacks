/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProperIsoOverPuncturedSpectrum
import StacksCheckRecall

/-!
# Closed immersions detected on the special fibre

In the category of proper algebraic spaces over the spectrum of a Noetherian
local ring that are isomorphisms over the punctured spectrum, a morphism is a
closed immersion as soon as the induced map of special fibres is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 89.2.2 Let `(A, 𝔪, κ)` be a Noetherian local ring. Let `g : X ⟶ Y` be
a morphism in the category `ProperIsoOverPuncturedSpectrum A` (89.2.0.1). If
the induced morphism of special fibres
`overBaseChange g q (residueFieldHom (Spec (.of A)) (IsLocalRing.closedPoint A))`
is a closed immersion, then `g` is a closed immersion. -/
@[stacks 0AGM]
#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_specialFiber :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X Y : AlgebraicSpace (Spec (.of A))} (g : X ⟶ Y) (q : Y ⟶ specSpace A)
    (hX : IsProperIsoOverOpen (g ≫ q) (puncturedι A))
    (hY : IsProperIsoOverOpen q (puncturedι A))
    [IsClosedImmersion
      (overBaseChange g q (residueFieldHom (Spec (.of A)) (IsLocalRing.closedPoint A)))],
    IsClosedImmersion g)

end AlgebraicGeometry.AlgebraicSpace
