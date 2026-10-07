module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale
public import ReasLib.CategoryTheory.Galois.Functoriality
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

@[expose] public section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]

/-- Two geometric points of a connected scheme have isomorphic finite étale fiber functors. -/
theorem existsIso_finiteFiber (xbar xbar' : GeometricPoint X) :
    Nonempty (finiteFiber xbar ≅ finiteFiber xbar') := sorry

/-- Conjugation by a fiber isomorphism is continuous for the canonical automorphism topologies. -/
theorem continuous_conjAut {xbar xbar' : GeometricPoint X}
    (t : finiteFiber xbar ≅ finiteFiber xbar') : Continuous t.conjAut := sorry

/-- A fiber isomorphism induces a continuous isomorphism of geometric fundamental groups. -/
noncomputable def autEquiv {xbar xbar' : GeometricPoint X}
    (t : finiteFiber xbar ≅ finiteFiber xbar') :
    Aut (finiteFiber xbar) ≃ₜ* Aut (finiteFiber xbar') where
  toMulEquiv := t.conjAut
  continuous_toFun := continuous_conjAut t
  continuous_invFun := continuous_conjAut t.symm

/-- The continuous homomorphism underlying a change of geometric base point. -/
noncomputable def autHom {xbar xbar' : GeometricPoint X}
    (t : finiteFiber xbar ≅ finiteFiber xbar') :
    Aut (finiteFiber xbar) →ₜ* Aut (finiteFiber xbar') :=
  ContinuousMonoidHom.toContinuousMonoidHom (autEquiv t)

/-- Changing the fiber isomorphism changes the fundamental-group isomorphism by inner conjugation. -/
theorem autEquiv_conj {xbar xbar' : GeometricPoint X}
    (t t' : finiteFiber xbar ≅ finiteFiber xbar') :
    ∃ g : Aut (finiteFiber xbar'), ∀ σ : Aut (finiteFiber xbar),
      autEquiv t' σ = g * autEquiv t σ * g⁻¹ := sorry

/-- Change of geometric base point is compatible with the finite continuous action functors. -/
theorem autEquiv_catCommSq {xbar xbar' : GeometricPoint X}
    (t : finiteFiber xbar ≅ finiteFiber xbar') :
    Nonempty (CatCommSq (𝟭 (Scheme.FiniteEtale X)) (fiberAction xbar') (fiberAction xbar)
      (ContAction.res FintypeCat (autHom t))) := sorry

/-- A morphism of connected schemes induces the canonical continuous fundamental-group homomorphism. -/
noncomputable def fundamentalGroupMap (f : X ⟶ Y) (xbar : GeometricPoint X) :
    Aut (finiteFiber xbar) →ₜ* Aut (finiteFiber (map xbar f)) :=
  inducedContinuousHomCore (finiteFiber (map xbar f)) (finiteFiber xbar)
    (Scheme.finiteEtaleBaseChange f) (finiteFiberBaseChangeIso f xbar)

/-- Restriction of finite continuous actions along the fundamental-group homomorphism of a scheme morphism. -/
noncomputable def fundamentalGroupRestriction (f : X ⟶ Y) (xbar : GeometricPoint X) :
    ContAction FintypeCat (Aut (finiteFiber (map xbar f))) ⥤
      ContAction FintypeCat (Aut (finiteFiber xbar)) :=
  ContAction.res FintypeCat (fundamentalGroupMap f xbar)

/-- Finite étale base change is compatible with restriction along the induced fundamental-group homomorphism. -/
theorem fundamentalGroupMap_catCommSq (f : X ⟶ Y) (xbar : GeometricPoint X) :
    Nonempty (CatCommSq (Scheme.finiteEtaleBaseChange f)
      (fiberAction (map xbar f)) (fiberAction xbar) (fundamentalGroupRestriction f xbar)) := sorry

/-- For a connected scheme, stabilizers of geometric finite-fiber points form an open
neighborhood basis at the identity of the automorphism group of the finite-fiber functor. -/
theorem finiteFiber_nhds_one_has_basis_stabilizers
    {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X) :
    (nhds (1 : Aut (finiteFiber xbar))).HasBasis
        (fun _ : (Σ Y : FiniteEtale X, (finiteFiber xbar).obj Y) ↦ True)
        (fun p ↦ MulAction.stabilizer (Aut (finiteFiber xbar)) p.2) ∧
      ∀ (Y : FiniteEtale X) (y : (finiteFiber xbar).obj Y),
        IsOpen
          (MulAction.stabilizer (Aut (finiteFiber xbar)) y :
            Set (Aut (finiteFiber xbar))) := sorry

/-- The profinite automorphism group of the finite étale fiber functor at a geometric point. -/
noncomputable abbrev etaleFundamentalGroup (X : Scheme.{u})
    (xbar : GeometricPoint X) : ProfiniteGrp :=
  ProfiniteGrp.of (Aut xbar.finiteFiber)

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme

export GeometricPoint (etaleFundamentalGroup)

end AlgebraicGeometry.Scheme
