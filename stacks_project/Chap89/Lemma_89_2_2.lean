module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import stacks_project.Chap76.Lemma_76_23_5
public import stacks_project.Chap89.«89_2_0_1»

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

/-- Lemma 89.2.2 Let `(A, 𝔪, κ)` be a Noetherian local ring. Let `g : X ⟶ Y` be
a morphism in the category `ProperIsoOverPuncturedSpectrum A` (89.2.0.1). If
the induced morphism of special fibres
`overBaseChange g q (residueFieldHom (Spec (.of A)) (IsLocalRing.closedPoint A))`
is a closed immersion, then `g` is a closed immersion. -/
@[stacks 0AGM]
theorem IsClosedImmersion.of_specialFiber
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X Y : AlgebraicSpace (Spec (.of A))} (g : X ⟶ Y) (q : Y ⟶ specSpace A)
    (hX : IsProperIsoOverOpen (g ≫ q) (puncturedι A))
    (hY : IsProperIsoOverOpen q (puncturedι A))
    [IsClosedImmersion
      (overBaseChange g q (residueFieldHom (Spec (.of A)) (IsLocalRing.closedPoint A)))] :
    IsClosedImmersion g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
