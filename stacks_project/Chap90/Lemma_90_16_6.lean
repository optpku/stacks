/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger

/-!
# Rim-Schlessinger implies Schlessinger's conditions

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (RS),
then it satisfies Schlessinger's conditions (S1) and (S2).
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.16.6 (1): if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and satisfies (RS), then `p` satisfies Schlessinger's condition (S1). -/
@[stacks 06J7]
instance HasRimSchlessinger.toHasSchlessingerS1
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    HasSchlessingerS1 p := sorry

/-- Lemma 90.16.6 (2): if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and satisfies (RS), then `p` satisfies Schlessinger's condition (S2). -/
@[stacks 06J7]
instance HasRimSchlessinger.toHasSchlessingerS2
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    HasSchlessingerS2 p := sorry

end CategoryTheory.Functor
