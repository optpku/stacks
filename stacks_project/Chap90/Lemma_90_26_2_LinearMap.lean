module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import stacks_project.Chap90.Definition_90_19_2_DualNumber
public import stacks_project.Chap90.Example_90_11_10_TangentSpace
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero
public import stacks_project.Chap90.Lemma_90_12_2_Tensor
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap90.Lemma_90_26_2_Instances
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut

/-!
# Infinitesimal and tangent maps of a kernel-pair deformation functor

The connecting map `Inf(F) ⟶ T(R)` and the projection pair `T(R) ⟶ TU × TU` associated
to a morphism `f : U ⟶ F` from a deformation functor to a deformation category.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor
open Functor.Fiber

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
  left_inv := sorry
  right_inv := sorry

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

/-- The additive group structure on `G(k[ε])`, transported from `instAddCommGroup_obj_squareZero`
along `dualNumberIsoSquareZero`. -/
instance instAddCommGroup_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    AddCommGroup (G.obj (dualNumber Λ k)) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-module structure on `G(k[ε])`, transported from `instModule_obj_squareZero`
along `dualNumberIsoSquareZero`. -/
instance instModule_obj_dualNumber [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    Module k (G.obj (dualNumber Λ k)) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Addition on the tangent space of a predeformation functor. -/
instance instAddCommGroup_tangentSpace [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    AddCommGroup (IsPredeformationFunctor.tangentSpace G) :=
  instAddCommGroup_obj_dualNumber

/-- The `k`-module structure on the tangent space of a predeformation functor. -/
instance instModule_tangentSpace [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    Module k (IsPredeformationFunctor.tangentSpace G) :=
  instModule_obj_dualNumber

end CategoryTheory.Functor

variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.GroupoidInFunctors

/-- The unique residue-field value of a predeformation functor. -/
def residuePoint [IsPredeformationFunctor U] : U.obj (residue Λ k) :=
  default

variable (f : Functor.ofTypeValued U ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationFunctor U]

/-- The image of an object of `U` in `F` lies over the same base object. -/
theorem imageObj_over {T : ArtinianLocalAlgCat Λ k} (x : U.obj T) :
    F.p.obj (imageObj f T x) = T := sorry

/-- The fibre object of `F` over `T` corresponding to the image of an object of `U`. -/
def imageFiber {T : ArtinianLocalAlgCat Λ k} (x : U.obj T) : F.p.Fiber T :=
  ⟨imageObj f T x, imageObj_over f x⟩

/-- The residue-fibre object of `F` which is the image of the unique residue point of `U`. -/
def connectingResidueFiber : F.p.Fiber (residue Λ k) :=
  imageFiber f residuePoint

/-- The dual-number fibre object of `F` which is the image of the dual-number pushforward of
the unique residue point of `U`. -/
def connectingDualNumberFiber : F.p.Fiber (dualNumber Λ k) :=
  imageFiber f (U.map (residueToDualNumber Λ k) residuePoint)

/-- The image in `F` of the unique elements-arrow over `residueToDualNumber`. -/
def connectingLift :
    fiberInclusion.obj (connectingResidueFiber f) ⟶
      fiberInclusion.obj (connectingDualNumberFiber f) :=
  imageLift f (residueToDualNumber Λ k) residuePoint

/-- The connecting lift is strongly cocartesian over `residueToDualNumber`. -/
instance instIsStronglyCocartesian_connectingLift :
    F.p.IsStronglyCocartesian (residueToDualNumber Λ k) (connectingLift f) := sorry

/-- Transport of an infinitesimal automorphism of `F` to an automorphism of the dual-number
image of the unique residue point of `U`. -/
def connectingAut (α : infinitesimalAutomorphisms F.p) :
    Aut (connectingDualNumberFiber f) :=
  (infinitesimalAutomorphismsEquivAt F.p (connectingResidueFiber f)
      (connectingDualNumberFiber f) (connectingLift f) α).val

/-- The connecting map `Inf(F) ⟶ T(R)` sending an infinitesimal automorphism of `F` to the
kernel-pair arrow with both legs the dual-number pushforward of the unique residue point of
`U`, and with comparison the transported automorphism. -/
def connecting (α : infinitesimalAutomorphisms F.p) :
    IsPredeformationFunctor.tangentSpace (relation f) where
  left := U.map (residueToDualNumber Λ k) residuePoint
  right := U.map (residueToDualNumber Λ k) residuePoint
  hom := fiberInclusion.map (connectingAut f α).hom
  inv := fiberInclusion.map (connectingAut f α).inv
  hom_inv_id := sorry
  inv_hom_id := sorry
  hom_isHomLift := sorry
  inv_isHomLift := sorry

/-- The connecting map is `k`-linear. -/
theorem isLinearMap_connecting : IsLinearMap k (connecting f) := sorry

/-- The bundled `k`-linear connecting map `Inf(F) ⟶ T(relation f)`. -/
def connectingLinearMap :
    infinitesimalAutomorphisms F.p →ₗ[k]
      IsPredeformationFunctor.tangentSpace (relation f) :=
  IsLinearMap.mk' (connecting f) (isLinearMap_connecting f)

/-- The underlying function of `connectingLinearMap` is `connecting`. -/
theorem connectingLinearMap_apply (α : infinitesimalAutomorphisms F.p) :
    connectingLinearMap f α = connecting f α := sorry

/-- The dual-number component of `tgt f` is `k`-linear. -/
theorem isLinearMap_tgt_app :
    IsLinearMap k fun a : IsPredeformationFunctor.tangentSpace (relation f) =>
      (tgt f).app (dualNumber Λ k) a := sorry

/-- The dual-number component of `src f` is `k`-linear. -/
theorem isLinearMap_src_app :
    IsLinearMap k fun a : IsPredeformationFunctor.tangentSpace (relation f) =>
      (src f).app (dualNumber Λ k) a := sorry

/-- The pair of dual-number components of `tgt f` and `src f`, as a `k`-linear map
`T(relation f) →ₗ[k] TU × TU`. -/
def tangentProdLinearMap :
    IsPredeformationFunctor.tangentSpace (relation f) →ₗ[k]
      IsPredeformationFunctor.tangentSpace U ×
        IsPredeformationFunctor.tangentSpace U :=
  LinearMap.prod
    (IsLinearMap.mk' (fun a => (tgt f).app (dualNumber Λ k) a) (isLinearMap_tgt_app f))
    (IsLinearMap.mk' (fun a => (src f).app (dualNumber Λ k) a) (isLinearMap_src_app f))

/-- `tangentProdLinearMap` evaluates as the pair of dual-number components of `tgt` and `src`. -/
theorem tangentProdLinearMap_apply
    (a : IsPredeformationFunctor.tangentSpace (relation f)) :
    tangentProdLinearMap f a =
      ((tgt f).app (dualNumber Λ k) a, (src f).app (dualNumber Λ k) a) := sorry

/-- Infinitesimal automorphisms of a deformation functor vanish. -/
theorem infinitesimalAutomorphisms_ofTypeValued_subsingleton :
    Subsingleton (infinitesimalAutomorphisms (CategoryOfElements.π U)) := sorry

end CategoryTheory.GroupoidInFunctors
