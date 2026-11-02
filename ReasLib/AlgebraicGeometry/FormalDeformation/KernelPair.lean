/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.KernelPair
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.ExactSequence

/-!
# Deformation functors and the tangent sequence of a kernel pair

The kernel pair of a morphism from a deformation functor to a deformation category
is a deformation functor. Its tangent space receives the infinitesimal automorphisms
of the category, with image the kernel of the two tangent projections.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor
open Functor.Fiber

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.GroupoidInFunctors

/-- Infinitesimal automorphisms of a predeformation functor vanish. -/
private theorem infinitesimalAutomorphisms_ofTypeValued_subsingleton
    [IsPredeformationFunctor U] :
    Subsingleton (infinitesimalAutomorphisms (CategoryOfElements.π U)) := by
  refine ⟨fun α β => ?_⟩
  apply Iso.ext
  apply Fiber.hom_ext
  apply (CategoryOfElements.π U).map_injective
  rw [IsHomLift.fac' (CategoryOfElements.π U) (𝟙 (dualNumber Λ k))
      (fiberInclusion.map α.hom),
    IsHomLift.fac' (CategoryOfElements.π U) (𝟙 (dualNumber Λ k))
      (fiberInclusion.map β.hom)]

/-- The kernel pair of a morphism from a deformation functor to a deformation category
is a deformation functor. -/
instance instIsDeformationFunctor_relation (f : Functor.ofTypeValued U ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationFunctor U] :
    IsDeformationFunctor (relation f) := sorry

variable (f : Functor.ofTypeValued U ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationFunctor U]

/-- The fibre object of `F` over `T` corresponding to the image of an object of `U`. -/
def imageFiber {T : ArtinianLocalAlgCat Λ k} (x : U.obj T) : F.p.Fiber T :=
  ⟨imageObj f T x, imageObj_base f T x⟩

/-- The residue-fibre object of `F` which is the image of the unique residue point of `U`. -/
def connectingResidueFiber : F.p.Fiber (residue Λ k) :=
  imageFiber f (Functor.residuePoint U)

/-- The dual-number fibre object of `F` which is the image of the dual-number pushforward of
the unique residue point of `U`. -/
def connectingDualNumberFiber : F.p.Fiber (dualNumber Λ k) :=
  imageFiber f (U.map (residueToDualNumber Λ k) (Functor.residuePoint U))

/-- The image in `F` of the unique elements-arrow over `residueToDualNumber`. -/
def connectingLift :
    fiberInclusion.obj (connectingResidueFiber f) ⟶
      fiberInclusion.obj (connectingDualNumberFiber f) :=
  imageLift f (residueToDualNumber Λ k) (Functor.residuePoint U)

/-- The connecting lift is strongly cocartesian over `residueToDualNumber`. -/
instance instIsStronglyCocartesian_connectingLift :
    F.p.IsStronglyCocartesian (residueToDualNumber Λ k) (connectingLift f) :=
  imageLift_isStronglyCocartesian f (residueToDualNumber Λ k) (Functor.residuePoint U)

/-- Transport of an infinitesimal automorphism of `F` to an automorphism of the dual-number
image of the unique residue point of `U`. -/
def connectingAut (α : infinitesimalAutomorphisms F.p) :
    Aut (connectingDualNumberFiber f) :=
  (infinitesimalAutomorphismsEquivAt F.p (connectingResidueFiber f)
      (connectingDualNumberFiber f) (connectingLift f) α).val

/-- The comparison maps obtained from a transported infinitesimal automorphism are
mutually inverse and lie over the identity of the dual-number algebra. -/
private theorem connecting_laws (α : infinitesimalAutomorphisms F.p) :
    (fiberInclusion.map (connectingAut f α).hom ≫
      fiberInclusion.map (connectingAut f α).inv =
        𝟙 (imageObj f (dualNumber Λ k)
          (U.map (residueToDualNumber Λ k) (Functor.residuePoint U)))) ∧
    (fiberInclusion.map (connectingAut f α).inv ≫
      fiberInclusion.map (connectingAut f α).hom =
        𝟙 (imageObj f (dualNumber Λ k)
          (U.map (residueToDualNumber Λ k) (Functor.residuePoint U)))) ∧
    F.p.IsHomLift (𝟙 (dualNumber Λ k)) (fiberInclusion.map (connectingAut f α).hom) ∧
    F.p.IsHomLift (𝟙 (dualNumber Λ k)) (fiberInclusion.map (connectingAut f α).inv) := by
  exact ⟨(fiberInclusion.mapIso (connectingAut f α)).hom_inv_id,
    (fiberInclusion.mapIso (connectingAut f α)).inv_hom_id, inferInstance, inferInstance⟩

/-- The connecting map `Inf(F) ⟶ T(R)` sending an infinitesimal automorphism of `F` to the
kernel-pair arrow with both legs the dual-number pushforward of the unique residue point of
`U`, and with comparison the transported automorphism. -/
def connecting (α : infinitesimalAutomorphisms F.p) :
    IsPredeformationFunctor.tangentSpace (relation f) where
  left := U.map (residueToDualNumber Λ k) (Functor.residuePoint U)
  right := U.map (residueToDualNumber Λ k) (Functor.residuePoint U)
  hom := fiberInclusion.map (connectingAut f α).hom
  inv := fiberInclusion.map (connectingAut f α).inv
  hom_inv_id := by exact (connecting_laws f α).1
  inv_hom_id := by exact (connecting_laws f α).2.1
  hom_isHomLift := by exact (connecting_laws f α).2.2.1
  inv_isHomLift := by exact (connecting_laws f α).2.2.2

/-- The connecting map is `k`-linear. -/
theorem isLinearMap_connecting : IsLinearMap k (connecting f) := sorry

/-- The bundled `k`-linear connecting map `Inf(F) ⟶ T(relation f)`. -/
def connectingLinearMap :
    infinitesimalAutomorphisms F.p →ₗ[k]
      IsPredeformationFunctor.tangentSpace (relation f) :=
  IsLinearMap.mk' (connecting f) (isLinearMap_connecting f)

/-- The underlying function of `connectingLinearMap` is `connecting`. -/
theorem connectingLinearMap_apply (α : infinitesimalAutomorphisms F.p) :
    connectingLinearMap f α = connecting f α := rfl

private theorem squareZeroInverse_naturality
    {G H : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
    [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    [IsPredeformationFunctor H] [HasSchlessingerH2 H]
    (η : G ⟶ H) (x y : G.obj (squareZero Λ k k)) :
    η.app (squareZeroPullback (squareZero Λ k k) k)
        (squareZeroPullbackInverse G (squareZero Λ k k) k (objSquareZeroAddPair G x y)) =
      squareZeroPullbackInverse H (squareZero Λ k k) k
        (objSquareZeroAddPair H (η.app _ x) (η.app _ y)) := by
  apply (squareZeroPullbackInverse_spec H (squareZero Λ k k) k).1.injective
  rw [(squareZeroPullbackInverse_spec H (squareZero Λ k k) k).2]
  apply Subtype.ext
  apply Prod.ext
  · change H.map (squareZeroPullbackFst (squareZero Λ k k) k)
        (η.app _ (squareZeroPullbackInverse G _ _ (objSquareZeroAddPair G x y))) = η.app _ x
    rw [← NatTrans.naturality_apply]
    exact congrArg (fun z => η.app _ z)
      (congrArg (fun pair => pair.val.1)
        ((squareZeroPullbackInverse_spec G (squareZero Λ k k) k).2
          (objSquareZeroAddPair G x y)))
  · change H.map (squareZeroPullbackSnd (squareZero Λ k k) k)
        (η.app _ (squareZeroPullbackInverse G _ _ (objSquareZeroAddPair G x y))) = η.app _ y
    rw [← NatTrans.naturality_apply]
    exact congrArg (fun z => η.app _ z)
      (congrArg (fun pair => pair.val.2)
        ((squareZeroPullbackInverse_spec G (squareZero Λ k k) k).2
          (objSquareZeroAddPair G x y)))

private theorem squareZero_app_add
    {G H : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
    [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    [IsPredeformationFunctor H] [HasSchlessingerH2 H]
    (η : G ⟶ H) (x y : G.obj (squareZero Λ k k)) :
    η.app _ (x + y) = η.app _ x + η.app _ y := by
  change η.app _ (G.map (squareZeroSum k) _) = H.map (squareZeroSum k) _
  rw [NatTrans.naturality_apply, squareZeroInverse_naturality]

private theorem isLinearMap_app_dualNumber
    {G H : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
    [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    [IsPredeformationFunctor H] [HasSchlessingerH2 H]
    (η : G ⟶ H) :
    IsLinearMap k fun x : G.obj (dualNumber Λ k) => η.app _ x := by
  have natural (x : G.obj (squareZero Λ k k)) :
      η.app (dualNumber Λ k) ((objDualNumberEquivSquareZero G).symm x) =
        (objDualNumberEquivSquareZero H).symm (η.app _ x) :=
    NatTrans.naturality_apply η (dualNumberIsoSquareZero Λ k).inv x
  have natural' (x : G.obj (dualNumber Λ k)) :
      η.app (squareZero Λ k k) (objDualNumberEquivSquareZero G x) =
        objDualNumberEquivSquareZero H (η.app _ x) :=
    NatTrans.naturality_apply η (dualNumberIsoSquareZero Λ k).hom x
  constructor
  · intro x y
    change η.app _ ((objDualNumberEquivSquareZero G).symm
      (objDualNumberEquivSquareZero G x + objDualNumberEquivSquareZero G y)) =
        (objDualNumberEquivSquareZero H).symm
          (objDualNumberEquivSquareZero H (η.app _ x) +
            objDualNumberEquivSquareZero H (η.app _ y))
    rw [natural, squareZero_app_add, natural', natural']
  · intro r x
    change η.app _ ((objDualNumberEquivSquareZero G).symm
      (G.map (squareZeroMap (LinearMap.lsmul k k r))
        (objDualNumberEquivSquareZero G x))) =
      (objDualNumberEquivSquareZero H).symm
        (H.map (squareZeroMap (LinearMap.lsmul k k r))
          (objDualNumberEquivSquareZero H (η.app _ x)))
    rw [natural, NatTrans.naturality_apply, natural']

/-- The dual-number component of `tgt f` is `k`-linear. -/
theorem isLinearMap_tgt_app :
    IsLinearMap k fun a : IsPredeformationFunctor.tangentSpace (relation f) =>
      (tgt f).app (dualNumber Λ k) a :=
  isLinearMap_app_dualNumber (tgt f)

/-- The dual-number component of `src f` is `k`-linear. -/
theorem isLinearMap_src_app :
    IsLinearMap k fun a : IsPredeformationFunctor.tangentSpace (relation f) =>
      (src f).app (dualNumber Λ k) a :=
  isLinearMap_app_dualNumber (src f)

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
      ((tgt f).app (dualNumber Λ k) a, (src f).app (dualNumber Λ k) a) := rfl

private theorem tangentSpace_zero_eq
    {G : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
    [IsPredeformationFunctor G] [HasSchlessingerH2 G] :
    (0 : IsPredeformationFunctor.tangentSpace G) =
      G.map (residueToDualNumber Λ k) (residuePoint G) := by
  change G.map (dualNumberIsoSquareZero Λ k).inv
    (G.map (residueToSquareZero k) (residuePoint G)) = _
  rw [← G.map_comp_apply]
  congr 1

/-- The connecting map is injective, and its image is the kernel of the pair of
canonical tangent projections. -/
theorem infTangentSequence_exact :
    Function.Injective (connectingLinearMap f) ∧
      Function.Exact (connectingLinearMap f) (tangentProdLinearMap f) := by
  constructor
  · intro α β h
    apply (infinitesimalAutomorphismsEquivAt F.p (connectingResidueFiber f)
      (connectingDualNumberFiber f) (connectingLift f)).injective
    apply Subtype.ext
    apply Iso.ext
    apply Fiber.hom_ext
    have hom_heq (a b : Arrow f (dualNumber Λ k)) (hab : a = b) : HEq a.hom b.hom := by
      cases hab
      rfl
    exact eq_of_heq (hom_heq _ _ h)
  · intro a
    constructor
    · intro ha
      change (a.left, a.right) = (0, 0) at ha
      have hleft : a.left = U.map (residueToDualNumber Λ k) (residuePoint U) := by
        calc
          a.left = 0 := by simpa using congrArg (fun z => z.1) ha
          _ = U.map (residueToDualNumber Λ k) (residuePoint U) := tangentSpace_zero_eq
      have hright : a.right = U.map (residueToDualNumber Λ k) (residuePoint U) := by
        calc
          a.right = 0 := by simpa using congrArg (fun z => z.2) ha
          _ = U.map (residueToDualNumber Λ k) (residuePoint U) := tangentSpace_zero_eq
      obtain ⟨left, right, hom, inv, hom_inv_id, inv_hom_id, hom_lift, inv_lift⟩ := a
      dsimp only at hleft hright
      subst left right
      let aut : Aut (connectingDualNumberFiber f) :=
        { hom := ⟨hom, hom_lift⟩
          inv := ⟨inv, inv_lift⟩
          hom_inv_id := Subtype.ext hom_inv_id
          inv_hom_id := Subtype.ext inv_hom_id }
      let pointed : infinitesimalAutomorphismsAt F.p (connectingResidueFiber f)
          (connectingDualNumberFiber f) (connectingLift f) :=
        ⟨aut, by rw [infinitesimalAutomorphismsAt_eq_top]; trivial⟩
      let α := (infinitesimalAutomorphismsEquivAt F.p (connectingResidueFiber f)
        (connectingDualNumberFiber f) (connectingLift f)).symm pointed
      have hα : connectingAut f α = aut := by
        change ((infinitesimalAutomorphismsEquivAt F.p (connectingResidueFiber f)
          (connectingDualNumberFiber f) (connectingLift f))
            ((infinitesimalAutomorphismsEquivAt F.p (connectingResidueFiber f)
              (connectingDualNumberFiber f) (connectingLift f)).symm pointed)).val = aut
        rw [MulEquiv.apply_symm_apply]
      refine ⟨α, ?_⟩
      change connecting f α = _
      unfold connecting
      simp only [hα]
      rfl
    · rintro ⟨α, rfl⟩
      apply Prod.ext
      · exact (tangentSpace_zero_eq (G := U)).symm
      · exact (tangentSpace_zero_eq (G := U)).symm

end CategoryTheory.GroupoidInFunctors
