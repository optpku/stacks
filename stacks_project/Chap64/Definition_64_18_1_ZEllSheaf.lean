module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf
public import stacks_project.Chap59.Lemma_59_82_1

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- The shared stage projection retains the sequential inverse-system indexing. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stage :
  ZEllSheaf X ℓ → ℕ → Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/- The shared constant construction is a ℤ_[ℓ]-sheaf on the same small étale site. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constant X ℓ : ZEllSheaf X ℓ)

/- Morphisms retain the natural-transformation representation. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.Hom :
  ZEllSheaf X ℓ → ZEllSheaf X ℓ → Type (u + 1))

end AlgebraicGeometry.Scheme.Etale
