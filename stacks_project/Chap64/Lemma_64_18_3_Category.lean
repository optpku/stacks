module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import stacks_project.Chap64.Definition_64_18_1_ZEllSheaf

/-!
# Category and preadditive structure of ℤ_[ℓ]-sheaves

Morphisms of `ℤ_[ℓ]`-sheaves are morphisms of the underlying inverse systems, and Hom-groups
are those of sequential inverse systems of étale abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- Morphisms of `ℤ_[ℓ]`-sheaves are morphisms of the underlying inverse systems. -/
instance instCategory : Category (ZEllSheaf X ℓ) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Hom-groups of `ℤ_[ℓ]`-sheaves are the Hom-groups of inverse systems of étale
abelian sheaves. -/
instance instPreadditive : Preadditive (ZEllSheaf X ℓ) where
  homGroup F G := inferInstanceAs (AddCommGroup (F.system ⟶ G.system))
  add_comp := sorry
  comp_add := sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
