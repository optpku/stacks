module

public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Essential surjections in `ArtinianLocalAlgCat`

A morphism in `C_Λ` is an essential surjection when it is surjective and
cancels surjectivity on the left.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Definition 90.3.9: A morphism `f : B ⟶ A` in `C_Λ` is an essential surjection
if `f` is surjective, and every morphism `g : C ⟶ B` in `C_Λ` such that `g ≫ f`
is surjective is itself surjective. -/
@[stacks 06GF]
class IsEssentialSurjection {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) : Prop where
  /-- The underlying `Λ`-algebra map is surjective. -/
  surjective : Function.Surjective f.hom
  /-- If `g ≫ f` is surjective, then `g` is surjective. -/
  of_comp_surjective {C : ArtinianLocalAlgCat Λ k} (g : C ⟶ B)
    (hg : Function.Surjective (g ≫ f).hom) : Function.Surjective g.hom

/-- The identity morphism of an object of `ArtinianLocalAlgCat Λ k` is an essential
surjection. -/
instance IsEssentialSurjection.id {B : ArtinianLocalAlgCat Λ k} :
    IsEssentialSurjection (𝟙 B) := sorry

/-- A morphism in `ArtinianLocalAlgCat Λ k` is an essential surjection iff it is
surjective and left-cancels surjectivity. -/
theorem isEssentialSurjection_iff {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔
      Function.Surjective f.hom ∧
        ∀ {C : ArtinianLocalAlgCat Λ k} (g : C ⟶ B),
          Function.Surjective (g ≫ f).hom → Function.Surjective g.hom := sorry

end ArtinianLocalAlgCat
