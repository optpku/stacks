module

public import ReasLib.Algebra.Module.Torsion.LocalCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine

/-!
# Stalkwise detection of torsion-freeness

Torsion-freeness of quasicoherent module sheaves on integral schemes can be detected on their
stalks.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- A quasicoherent module sheaf on an integral scheme is torsion free exactly when every stalk
is torsion free over the corresponding local ring. -/
theorem isTorsionFree_iff_stalkwise
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree ℱ ↔
      ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x) := sorry

namespace IsTorsionFree

/-- Every stalk of a torsion-free quasicoherent module sheaf on an integral scheme is torsion
free over the corresponding local ring. -/
theorem stalk {ℱ : X.Modules} [ℱ.IsQuasicoherent]
    (hℱ : IsTorsionFree ℱ) (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x) :=
  (isTorsionFree_iff_stalkwise ℱ).1 hℱ x

/-- Stalks of a torsion-free quasicoherent module sheaf carry their canonical ring-theoretic
torsion-free instances. -/
instance instModuleIsTorsionFree_stalkModuleCat
    {ℱ : X.Modules} [ℱ.IsQuasicoherent] [hℱ : IsTorsionFree ℱ] (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x) :=
  hℱ.stalk x

end IsTorsionFree

/-- A quasicoherent module sheaf on an integral scheme is torsion free if every stalk is torsion
free over the corresponding local ring. -/
theorem isTorsionFree_of_stalkwise
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x)) :
    IsTorsionFree ℱ :=
  (isTorsionFree_iff_stalkwise ℱ).2 hℱ

end AlgebraicGeometry.Scheme.Modules
