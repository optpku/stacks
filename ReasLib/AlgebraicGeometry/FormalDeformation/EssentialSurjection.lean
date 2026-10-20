/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-!
# Essential surjections of Artinian local algebras

Essential surjections are surjective morphisms that cancel surjectivity of
composable morphisms into their domain.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- A morphism of Artinian local `Λ`-algebras is an essential surjection if it is
surjective and every morphism into its domain with surjective composite is surjective. -/
class IsEssentialSurjection {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) : Prop where
  /-- The underlying `Λ`-algebra map is surjective. -/
  surjective : Function.Surjective f.hom
  /-- If `g ≫ f` is surjective, then `g` is surjective. -/
  of_comp_surjective {C : ArtinianLocalAlgCat Λ k} (g : C ⟶ B)
    (hg : Function.Surjective (g ≫ f).hom) : Function.Surjective g.hom

/-- The identity morphism of an Artinian local `Λ`-algebra is an essential surjection. -/
instance IsEssentialSurjection.id {B : ArtinianLocalAlgCat Λ k} :
    IsEssentialSurjection (𝟙 B) := sorry

/-- A morphism of Artinian local `Λ`-algebras is an essential surjection exactly when
it is surjective and every morphism with surjective composite is surjective. -/
theorem isEssentialSurjection_iff {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔
      Function.Surjective f.hom ∧
        ∀ {C : ArtinianLocalAlgCat Λ k} (g : C ⟶ B),
          Function.Surjective (g ≫ f).hom → Function.Surjective g.hom := sorry

end ArtinianLocalAlgCat
