module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- The canonical full-subcategory category and preadditive structure remain
available through typeclass inference. -/
#check (inferInstance : Category (ZEllSheaf X ℓ))
#check (inferInstance : Preadditive (ZEllSheaf X ℓ))

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
