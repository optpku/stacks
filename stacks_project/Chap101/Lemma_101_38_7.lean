/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_38_1_SchemeTheoreticImage

/-!
# Scheme-theoretic image of a partial section of algebraic stacks

A section of a separated morphism of algebraic stacks, representable by
algebraic spaces, over a quasi-compact open immersion has scheme-theoretic
image mapping isomorphically to the target over that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/-- Lemma 101.38.7: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces and separated. Let `ιV : V ⟶ Y` be a
quasi-compact open immersion, and let `s : V ⟶ X` be a section of `f` over
`V`. If `ι : Y' ⟶ X` is a scheme-theoretic image of `s`, then `Y' ⟶ Y` is an
isomorphism over `V`. -/
@[stacks 0CPW]
theorem isIso_snd_of_section {S : Scheme.{u}}
    {X Y V Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack V] [AlgebraicStack Y']
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) [Separated f]
    (ιV : V ⟶ Y) [OpenImmersion ιV] [QuasiCompact ιV]
    (s : V ⟶ X) (hs : s ≫ f = ιV) (toImage : V ⟶ Y') (ι : Y' ⟶ X)
    [IsSchemeTheoreticImage s toImage ι] :
    IsIso (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (ι ≫ f) ιV) := sorry

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
