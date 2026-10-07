module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage

/-!
# Scheme-theoretic image of a partial section

A section of a separated morphism of algebraic spaces over a quasi-compact open
immersion has scheme-theoretic image mapping isomorphically to the target over
that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- Lemma 67.16.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a separated morphism
of algebraic spaces over `S`. Let `ιV : V ⟶ Y` be a quasi-compact open
immersion, and let `s : V ⟶ X` be a section of `f` over `V`. If `ι : Y' ⟶ X`
is a scheme-theoretic image of `s`, then `Y' ⟶ Y` is an isomorphism over `V`. -/
@[stacks 0CP3]
theorem isIso_openInverseImageTo_of_section {S : Scheme.{u}}
    {X Y V Y' : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    (ιV : V ⟶ Y) [IsOpenImmersion ιV] [QuasiCompact ιV]
    (s : V ⟶ X) (hs : s ≫ f = ιV) (toImage : V ⟶ Y') (ι : Y' ⟶ X)
    [IsSchemeTheoreticImage s toImage ι] :
    IsIso (openInverseImageTo (ι ≫ f) ιV) := sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
