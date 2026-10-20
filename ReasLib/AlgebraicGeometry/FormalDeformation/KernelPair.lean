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
    Subsingleton (infinitesimalAutomorphisms (CategoryOfElements.π U)) := sorry

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
    F.p.IsHomLift (𝟙 (dualNumber Λ k)) (fiberInclusion.map (connectingAut f α).inv) := sorry

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
      ((tgt f).app (dualNumber Λ k) a, (src f).app (dualNumber Λ k) a) := rfl

/-- The connecting map is injective, and its image is the kernel of the pair of
canonical tangent projections. -/
theorem infTangentSequence_exact :
    Function.Injective (connectingLinearMap f) ∧
      Function.Exact (connectingLinearMap f) (tangentProdLinearMap f) := sorry

end CategoryTheory.GroupoidInFunctors
