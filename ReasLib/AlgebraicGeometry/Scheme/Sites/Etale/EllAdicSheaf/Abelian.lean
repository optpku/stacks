module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Limits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The abelian structure on ℓ-adic sheaves
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The coimage-image comparison of a morphism of ℓ-adic sheaves is an isomorphism. -/
instance instIsIso_coimageImageComparison {F G : ZEllSheaf X ℓ} (α : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison α) := sorry

/-- The category of ℓ-adic sheaves on a Noetherian scheme is abelian. -/
instance instAbelian : Abelian (ZEllSheaf X ℓ) :=
  Abelian.ofCoimageImageComparisonIsIso

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
