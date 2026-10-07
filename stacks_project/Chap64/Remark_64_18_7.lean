module

public import stacks_project.Chap64.Remark_64_18_7_ZEllSheaf
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

/-- Remark 64.18.7: on a Noetherian scheme, a `ℤ_[ℓ]`-sheaf is torsion if and only if
every geometric stalk is a torsion `ℤ_[ℓ]`-module. -/
@[stacks 03US]
theorem isTorsion_iff_forall_stalk_isTorsion
    {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (F : ZEllSheaf X ℓ) :
    F.IsTorsion ↔ ∀ x : GeometricPoint X, Module.IsTorsion ℤ_[ℓ] (F.stalk x) := sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
