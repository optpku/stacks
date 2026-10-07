module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Lemma_90_14_1_Pushforward
public import stacks_project.Chap90.Lemma_90_14_1_SubringOver

/-!
# Lemma 90.14.1

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies (S1), then
pushforward along `φ : y ⟶ x` sends minimal objects of `S_y` to minimal objects of `S_x`.
If moreover `p.map φ` is surjective, every minimal object of `S_x` is isomorphic to the
pushforward of some minimal object of `S_y`.
-/

@[expose] public section

open CategoryTheory
open Functor
open Functor.SubringOver

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor.SubringOver

/-- Lemma 90.14.1 (1): if `p` is cofibered in groupoids and has (S1), then for `φ : y ⟶ x`
the pushforward functor `S_y ⥤ S_x` sends minimal objects to minimal objects. -/
@[stacks 06T1]
theorem pushforward_preserves_isMinimal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] {x y : F} (φ : y ⟶ x)
    {a : SubringOver p y} (ha : IsMinimal a) :
    IsMinimal ((pushforward p φ).obj a) := sorry

/-- Lemma 90.14.1 (2): if `p` is cofibered in groupoids and has (S1), and `φ : y ⟶ x` lies
over a surjection, then every minimal object of `S_x` is isomorphic to the pushforward of
some minimal object of `S_y`. -/
@[stacks 06T1]
theorem exists_isMinimal_of_surjective (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] {x y : F} (φ : y ⟶ x)
    (hφ : Function.Surjective (p.map φ).hom) (a : SubringOver p x) (ha : IsMinimal a) :
    ∃ b : SubringOver p y, IsMinimal b ∧ Nonempty ((pushforward p φ).obj b ≅ a) := sorry

end CategoryTheory.Functor.SubringOver
