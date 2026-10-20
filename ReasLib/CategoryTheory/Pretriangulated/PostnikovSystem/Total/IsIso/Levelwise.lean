module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.IsLevelwiseIso.Base
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.IsIso.Basic

/-!
# Levelwise Isomorphisms in the Total Postnikov-System Category

This file derives total-category invertibility from levelwise invertibility of
the carried Postnikov-system morphism. It also constructs an isomorphism when
the base isomorphism is supplied as explicit data.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {n : ℕ} {P Q : Total D n}

/-- Levelwise invertibility of the system component implies invertibility in the total
category. -/
@[stacks 0D7Z]
theorem isIso_of_levelwise (f : P ⟶ Q)
    (hsystem : f.systemMap.IsLevelwiseIso) : IsIso f := sorry

/-- Assemble a total-category isomorphism directly from an isomorphism of finite rows and a
compatible levelwise-isomorphic map of Postnikov systems. -/
@[stacks 0D7Z "total Postnikov-system isomorphism from base and system data"]
noncomputable def isoMk (e : P.base ≅ Q.base)
    (ψ : PostnikovSystem.Morphism P.system Q.system e.hom)
    (hψ : ψ.IsLevelwiseIso) : P ≅ Q :=
  isoOfComponents { base := e.hom, systemMap := ψ }
    (inferInstance : IsIso e.hom) hψ

/-- The base component of the forward map of `isoMk` is the supplied base isomorphism. -/
@[simp, stacks 0D7Z]
theorem isoMk_hom_base (e : P.base ≅ Q.base)
    (ψ : PostnikovSystem.Morphism P.system Q.system e.hom)
    (hψ : ψ.IsLevelwiseIso) :
    (isoMk e ψ hψ).hom.base = e.hom := sorry

/-- The system component of the forward map of `isoMk` is the supplied system morphism. -/
@[simp, stacks 0D7Z]
theorem isoMk_hom_systemMap (e : P.base ≅ Q.base)
    (ψ : PostnikovSystem.Morphism P.system Q.system e.hom)
    (hψ : ψ.IsLevelwiseIso) :
    (isoMk e ψ hψ).hom.systemMap = ψ := sorry

/-- The base component of the inverse map of `isoMk` is the supplied inverse base map. -/
@[simp, stacks 0D7Z]
theorem isoMk_inv_base (e : P.base ≅ Q.base)
    (ψ : PostnikovSystem.Morphism P.system Q.system e.hom)
    (hψ : ψ.IsLevelwiseIso) :
    (isoMk e ψ hψ).inv.base = e.inv := sorry

/-- An auxiliary component of the inverse map of `isoMk` is the inverse of the corresponding
explicit component isomorphism. -/
@[simp, stacks 0D7Z]
theorem isoMk_inv_yMap (e : P.base ≅ Q.base)
    (ψ : PostnikovSystem.Morphism P.system Q.system e.hom)
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) :
    (isoMk e ψ hψ).inv.systemMap.yMap i = (hψ.yIso i).inv := sorry

/-- The system component of an invertible total morphism is levelwise invertible. -/
@[stacks 0D7Z "levelwise system map of a total Postnikov-system isomorphism"]
theorem systemMapIsLevelwiseIso (f : P ⟶ Q) [IsIso f] :
    f.systemMap.IsLevelwiseIso := sorry

/-- A total morphism is invertible exactly when its system component is levelwise invertible.
The base condition is a consequence of the Postnikov triangles. -/
@[stacks 0D7Z "levelwise criterion for total Postnikov-system isomorphisms"]
theorem isIso_iff_levelwise (f : P ⟶ Q) :
    IsIso f ↔ f.systemMap.IsLevelwiseIso := sorry

end CategoryTheory.PostnikovSystem.Total
