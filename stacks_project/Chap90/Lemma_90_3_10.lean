/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_3_9
public import stacks_project.Chap90.Lemma_90_3_10_ModSquare

/-!
# Essential surjections modulo squares

A morphism in `C_Λ` is an essential surjection if and only if the induced maps
on quotients by `maximalIdeal ^ 2` and by `relativeDenom` are essential
surjections.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Lemma 90.3.10 (1): a morphism `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k` is an
essential surjection if and only if the induced map `modSquareMap f` is an
essential surjection. -/
@[stacks 06S5]
theorem isEssentialSurjection_iff_modSquare {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ IsEssentialSurjection (modSquareMap f) := sorry

/-- Lemma 90.3.10 (2): a morphism `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k` is an
essential surjection if and only if the induced map `modRelativeMap f` is an
essential surjection. -/
@[stacks 06S5]
theorem isEssentialSurjection_iff_modRelative {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ IsEssentialSurjection (modRelativeMap f) := sorry

/-- Essential surjectivity of `modSquareMap f` is equivalent to essential surjectivity
of `modRelativeMap f`. -/
theorem isEssentialSurjection_modSquare_iff_modRelative {B A : ArtinianLocalAlgCat Λ k}
    (f : B ⟶ A) :
    IsEssentialSurjection (modSquareMap f) ↔ IsEssentialSurjection (modRelativeMap f) :=
  sorry

end ArtinianLocalAlgCat
