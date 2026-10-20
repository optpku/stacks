module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale

/-! Automorphisms of a specified geometric source field act on its finite étale fibers. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- Precompose lifts with a specified automorphism of their actual source spectrum. -/
def finiteFiberAut {X : Scheme.{u}} (s : GeometricPoint X)
    (τ : Spec (.of s.K) ≅ Spec (.of s.K)) (hτ : τ.hom ≫ s.hom = s.hom) :
    Aut s.finiteFiber :=
  NatIso.ofComponents (fun V : Scheme.FiniteEtale X ↦
    { hom := FintypeCat.homMk (fun (a : Over.mk s.hom ⟶ Over.mk V.hom) ↦
        Over.homMk (τ.hom ≫ a.left)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f ↦ τ.hom ≫ f) a.w).trans hτ)))
      inv := FintypeCat.homMk (fun (a : Over.mk s.hom ⟶ Over.mk V.hom) ↦
        Over.homMk (τ.inv ≫ a.left) (by
          have hi : τ.inv ≫ s.hom = s.hom := by
            calc
              τ.inv ≫ s.hom = τ.inv ≫ τ.hom ≫ s.hom := congrArg (τ.inv ≫ ·) hτ.symm
              _ = s.hom := τ.inv_hom_id_assoc _
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun f ↦ τ.inv ≫ f) a.w).trans hi)))
      hom_inv_id := by sorry
      inv_hom_id := by sorry }) (fun _ ↦ by sorry)

theorem finiteFiberAut_apply {X : Scheme.{u}} (s : GeometricPoint X)
    (τ : Spec (.of s.K) ≅ Spec (.of s.K)) (hτ : τ.hom ≫ s.hom = s.hom)
    (V : Scheme.FiniteEtale X) (a : s.finiteFiber.obj V) :
    ((finiteFiberAut s τ hτ).hom.app V a).left = τ.hom ≫ a.left := rfl

end AlgebraicGeometry.Scheme.GeometricPoint
