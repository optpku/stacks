module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TangentSpace

/-!
# Dual-number values of predeformation functors

Evaluation at dual numbers transports the square-zero vector space structure along
its canonical algebra isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

variable {G : ArtinianLocalAlgCat Λ k ⥤ Type w}

/-- Transport of values along the identification `k[ε] ≅ k[k]`. -/
def objDualNumberEquivSquareZero (G : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    G.obj (dualNumber Λ k) ≃ G.obj (squareZero Λ k k) where
  toFun := G.map (dualNumberIsoSquareZero Λ k).hom
  invFun := G.map (dualNumberIsoSquareZero Λ k).inv
  left_inv x := by
    change G.map (dualNumberIsoSquareZero Λ k).inv
      (G.map (dualNumberIsoSquareZero Λ k).hom x) = x
    rw [← G.map_comp_apply, Iso.hom_inv_id, G.map_id_apply]
  right_inv x := by
    change G.map (dualNumberIsoSquareZero Λ k).hom
      (G.map (dualNumberIsoSquareZero Λ k).inv x) = x
    rw [← G.map_comp_apply, Iso.inv_hom_id, G.map_id_apply]

/-- Addition on `G(k[ε])`, transported from `G(k[k])`. -/
instance instAdd_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    Add (G.obj (dualNumber Λ k)) where
  add x y :=
    (objDualNumberEquivSquareZero G).symm
      (objDualNumberEquivSquareZero G x + objDualNumberEquivSquareZero G y)

/-- Zero on `G(k[ε])`, transported from `G(k[k])`. -/
instance instZero_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    Zero (G.obj (dualNumber Λ k)) where
  zero := (objDualNumberEquivSquareZero G).symm 0

/-- Negation on `G(k[ε])`, transported from `G(k[k])`. -/
instance instNeg_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    Neg (G.obj (dualNumber Λ k)) where
  neg x := (objDualNumberEquivSquareZero G).symm (-objDualNumberEquivSquareZero G x)

/-- Scalar multiplication on `G(k[ε])`, transported from `G(k[k])`. -/
instance instSMul_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    SMul k (G.obj (dualNumber Λ k)) where
  smul r x := (objDualNumberEquivSquareZero G).symm (r • objDualNumberEquivSquareZero G x)

/-- The transported addition, zero, and negation on dual-number values satisfy the
abelian group laws. -/
theorem objDualNumber_addCommGroup_laws [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    (∀ x y z : G.obj (dualNumber Λ k), (x + y) + z = x + (y + z)) ∧
    (∀ x : G.obj (dualNumber Λ k), 0 + x = x) ∧
    (∀ x : G.obj (dualNumber Λ k), x + 0 = x) ∧
    (∀ x : G.obj (dualNumber Λ k), -x + x = 0) ∧
    (∀ x y : G.obj (dualNumber Λ k), x + y = y + x) := sorry

/-- The additive group structure on `G(k[ε])`, transported from `instAddCommGroup_obj_squareZero`
along `dualNumberIsoSquareZero`. -/
instance instAddCommGroup_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    AddCommGroup (G.obj (dualNumber Λ k)) where
  add_assoc := (objDualNumber_addCommGroup_laws (G := G)).1
  zero_add := (objDualNumber_addCommGroup_laws (G := G)).2.1
  add_zero := (objDualNumber_addCommGroup_laws (G := G)).2.2.1
  nsmul := nsmulRec
  neg_add_cancel := (objDualNumber_addCommGroup_laws (G := G)).2.2.2.1
  zsmul := zsmulRec
  add_comm := (objDualNumber_addCommGroup_laws (G := G)).2.2.2.2

/-- The transported scalar action on dual-number values satisfies the module laws. -/
theorem objDualNumber_module_laws [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    (∀ x : G.obj (dualNumber Λ k), (1 : k) • x = x) ∧
    (∀ r s : k, ∀ x : G.obj (dualNumber Λ k), (r * s) • x = r • (s • x)) ∧
    (∀ r : k, r • (0 : G.obj (dualNumber Λ k)) = 0) ∧
    (∀ r : k, ∀ x y : G.obj (dualNumber Λ k), r • (x + y) = r • x + r • y) ∧
    (∀ r s : k, ∀ x : G.obj (dualNumber Λ k), (r + s) • x = r • x + s • x) ∧
    (∀ x : G.obj (dualNumber Λ k), (0 : k) • x = 0) := sorry

/-- The `k`-module structure on `G(k[ε])`, transported from `instModule_obj_squareZero`
along `dualNumberIsoSquareZero`. -/
instance instModule_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    Module k (G.obj (dualNumber Λ k)) where
  one_smul := (objDualNumber_module_laws (G := G)).1
  mul_smul := (objDualNumber_module_laws (G := G)).2.1
  smul_zero := (objDualNumber_module_laws (G := G)).2.2.1
  smul_add := (objDualNumber_module_laws (G := G)).2.2.2.1
  add_smul := (objDualNumber_module_laws (G := G)).2.2.2.2.1
  zero_smul := (objDualNumber_module_laws (G := G)).2.2.2.2.2

/-- Addition on the tangent space of a predeformation functor. -/
instance instAddCommGroup_tangentSpace [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    AddCommGroup (IsPredeformationFunctor.tangentSpace G) :=
  instAddCommGroup_obj_dualNumber

/-- The `k`-module structure on the tangent space of a predeformation functor. -/
instance instModule_tangentSpace [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    Module k (IsPredeformationFunctor.tangentSpace G) :=
  instModule_obj_dualNumber

end CategoryTheory.Functor

