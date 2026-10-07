module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cup products on derived sections over global scalars

This leaf specializes the reusable tensor-compatible adjunction model to derived sections on a
ringed space.  It names the global and open cup-product maps and records their compatibility with
the two-open Mayer--Vietoris triangles.  The numbered chapter only recalls this owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

variable {X : RingedSpace.{u}}

/-- A tensor-compatible adjunction model for derived sections on an open subset. -/
@[stacks 0G6X "open derived-sections tensor model"]
abbrev TensorModel (X : RingedSpace.{u}) [ModuleDerived.Tensor.Has X]
    (U : Opens X.carrier) :=
  CategoryTheory.Adjunction.TensorModel
    (derived X U) (ModuleDerived.Tensor.globalSectionsCurried X)
      (ModuleDerived.Tensor.curried X)

/-- A tensor-compatible adjunction model for derived global sections. -/
@[stacks 0G6X "derived global-sections tensor model"]
abbrev GlobalTensorModel (X : RingedSpace.{u}) [ModuleDerived.Tensor.Has X] :=
  CategoryTheory.Adjunction.TensorModel
    (globalDerived X) (ModuleDerived.Tensor.globalSectionsCurried X)
      (ModuleDerived.Tensor.curried X)

/-- The cup-product map on an open, after restricting its coefficient factor from global
sections. -/
@[stacks 0G6X "open derived-sections cup product"]
noncomputable def cupProduct [ModuleDerived.Tensor.Has X] (U : Opens X.carrier)
    (P : TensorModel X U) (K M : ModuleDerived X) :
    ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).obj
        ((derived X U).obj M) ⟶
      (derived X U).obj (((ModuleDerived.Tensor.curried X).obj K).obj M) :=
  ((ModuleDerived.Tensor.globalSectionsCurried X).map
      ((derivedRestriction X U).app K)).app ((derived X U).obj M) ≫
    P.cupProduct K M

/-- The cup-product map on derived global sections. -/
@[stacks 0G6X "derived global-sections cup product"]
noncomputable abbrev globalCupProduct [ModuleDerived.Tensor.Has X]
    (P : GlobalTensorModel X) (K M : ModuleDerived X) :
    ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).obj
        ((globalDerived X).obj M) ⟶
      (globalDerived X).obj (((ModuleDerived.Tensor.curried X).obj K).obj M) :=
  P.cupProduct K M

/-- The middle object of the two-open derived-sections Mayer--Vietoris map. -/
@[stacks 0G6X "Mayer--Vietoris middle object"]
abbrev middle (X : RingedSpace.{u}) (U V : Opens X.carrier) (M : ModuleDerived X) :=
  (derived X U).obj M ⊞ (derived X V).obj M

/-- The source Mayer--Vietoris triangle used by the tensor comparison. -/
@[stacks 0G6X "source Mayer--Vietoris triangle"]
abbrev sourceTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (M : ModuleDerived X)
    (δ : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    Triangle (ModuleDerived.Tensor.globalSectionsDerived X) :=
  Triangle.mk ((mayerVietorisToBiprod X U V).app M)
    ((mayerVietorisDifference X U V).app M) (δ.app M)

/-- The target Mayer--Vietoris triangle used by the tensor comparison. -/
@[stacks 0G6X "target Mayer--Vietoris triangle"]
abbrev targetTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    [ModuleDerived.Tensor.Has X] (K M : ModuleDerived X)
    (δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    Triangle (ModuleDerived.Tensor.globalSectionsDerived X) :=
  Triangle.mk ((mayerVietorisToBiprod X U V).app
      (((ModuleDerived.Tensor.curried X).obj K).obj M))
    ((mayerVietorisDifference X U V).app
      (((ModuleDerived.Tensor.curried X).obj K).obj M))
    (δ'.app (((ModuleDerived.Tensor.curried X).obj K).obj M))

/-- The source triangle's middle object is the canonical open-section biproduct. -/
@[stacks 0G6X "source triangle middle object"]
theorem sourceTriangle_obj₂_eq (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (M : ModuleDerived X)
    (δ : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    (sourceTriangle X U V M δ).obj₂ = middle X U V M := sorry

/-- The source triangle's first object is the global derived section of `M`. -/
@[stacks 0G6X "source triangle first object"]
theorem sourceTriangle_obj₁_eq (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (M : ModuleDerived X)
    (δ : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    (sourceTriangle X U V M δ).obj₁ = (globalDerived X).obj M := sorry

/-- The source triangle's third object is the derived section over the overlap. -/
@[stacks 0G6X "source triangle third object"]
theorem sourceTriangle_obj₃_eq (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (M : ModuleDerived X)
    (δ : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    (sourceTriangle X U V M δ).obj₃ = (derived X (U ⊓ V)).obj M := sorry

/-- The target triangle's middle object is the tensor of the two open-section terms. -/
@[stacks 0G6X "target triangle middle object"]
theorem targetTriangle_obj₂_eq (X : RingedSpace.{u}) (U V : Opens X.carrier)
    [ModuleDerived.Tensor.Has X]
    (K M : ModuleDerived X)
    (δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    (targetTriangle X U V K M δ').obj₂ =
      middle X U V (((ModuleDerived.Tensor.curried X).obj K).obj M) := sorry

/-- The target triangle's first object is the global derived tensor term. -/
@[stacks 0G6X "target triangle first object"]
theorem targetTriangle_obj₁_eq (X : RingedSpace.{u}) (U V : Opens X.carrier)
    [ModuleDerived.Tensor.Has X] (K M : ModuleDerived X)
    (δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    (targetTriangle X U V K M δ').obj₁ =
      (globalDerived X).obj (((ModuleDerived.Tensor.curried X).obj K).obj M) := sorry

/-- The target triangle's third object is the derived tensor term over the overlap. -/
@[stacks 0G6X "target triangle third object"]
theorem targetTriangle_obj₃_eq (X : RingedSpace.{u}) (U V : Opens X.carrier)
    [ModuleDerived.Tensor.Has X] (K M : ModuleDerived X)
    (δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)) :
    (targetTriangle X U V K M δ').obj₃ =
      (derived X (U ⊓ V)).obj (((ModuleDerived.Tensor.curried X).obj K).obj M) := sorry

/-- The middle component of the cup-product map between two-open Mayer--Vietoris triangles. -/
@[stacks 0G6X "Mayer--Vietoris biproduct cup product"]
noncomputable def biprodCupProduct [ModuleDerived.Tensor.Has X]
    (U V : Opens X.carrier) (P_U : TensorModel X U) (P_V : TensorModel X V)
    (K M : ModuleDerived X) :
    ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).obj
        (middle X U V M) ⟶
      middle X U V (((ModuleDerived.Tensor.curried X).obj K).obj M) :=
  (((ModuleDerived.Tensor.globalSectionsCurried X).obj
      ((globalDerived X).obj K)).mapBiprod ((derived X U).obj M) ((derived X V).obj M)).hom ≫
    biprod.map (cupProduct U P_U K M) (cupProduct V P_V K M)

/-- The middle component transported to the exact object fields of the triangle morphism. -/
@[stacks 0G6X "transported Mayer--Vietoris middle component"]
noncomputable def biprodComponent [ModuleDerived.Tensor.Has X]
    (U V : Opens X.carrier) (P_U : TensorModel X U) (P_V : TensorModel X V)
    (K M : ModuleDerived X)
    (δ δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ))
    [((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).CommShift ℤ] :
    (((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).mapTriangle.obj
        (sourceTriangle X U V M δ)).obj₂ ⟶ (targetTriangle X U V K M δ').obj₂ :=
  eqToHom (CategoryTheory.Functor.mapTriangle_obj₂_eq
      ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K))
      (sourceTriangle X U V M δ)) ≫
    eqToHom (congrArg
      (fun Z ↦ ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).obj Z)
      (sourceTriangle_obj₂_eq X U V M δ)) ≫
    biprodCupProduct U V P_U P_V K M ≫
      eqToHom (targetTriangle_obj₂_eq X U V K M δ').symm

/-- The first component transported to the exact object fields of the triangle morphism. -/
@[stacks 0G6X "transported Mayer--Vietoris first component"]
noncomputable def globalComponent [ModuleDerived.Tensor.Has X]
    (global : GlobalTensorModel X) (U V : Opens X.carrier) (K M : ModuleDerived X)
    (δ δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ))
    [((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).CommShift ℤ] :
    (((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).mapTriangle.obj
        (sourceTriangle X U V M δ)).obj₁ ⟶ (targetTriangle X U V K M δ').obj₁ :=
  eqToHom (CategoryTheory.Functor.mapTriangle_obj₁_eq
      ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K))
      (sourceTriangle X U V M δ)) ≫
    eqToHom (congrArg
      (fun Z ↦ ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).obj Z)
      (sourceTriangle_obj₁_eq X U V M δ)) ≫
    globalCupProduct global K M ≫
      eqToHom (targetTriangle_obj₁_eq X U V K M δ').symm

/-- The third component transported to the exact object fields of the triangle morphism. -/
@[stacks 0G6X "transported Mayer--Vietoris third component"]
noncomputable def overlapComponent [ModuleDerived.Tensor.Has X]
    (P_UV : TensorModel X (U ⊓ V)) (K M : ModuleDerived X)
    (δ δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ))
    [((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).CommShift ℤ] :
    (((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).mapTriangle.obj
        (sourceTriangle X U V M δ)).obj₃ ⟶ (targetTriangle X U V K M δ').obj₃ :=
  eqToHom (CategoryTheory.Functor.mapTriangle_obj₃_eq
      ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K))
      (sourceTriangle X U V M δ)) ≫
  eqToHom (congrArg
      (fun Z ↦ ((ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)).obj Z)
      (sourceTriangle_obj₃_eq X U V M δ)) ≫
    cupProduct (U ⊓ V) P_UV K M ≫
      eqToHom (targetTriangle_obj₃_eq X U V K M δ').symm

namespace MayerVietoris

/-- The fixed-factor derived tensor functor acting on a Mayer--Vietoris triangle. -/
@[stacks 0G6X "fixed-factor tensor functor on a Mayer--Vietoris triangle"]
abbrev tensorFunctor (X : RingedSpace.{u}) [ModuleDerived.Tensor.Has X]
    (K : ModuleDerived X) :
    ModuleDerived.Tensor.globalSectionsDerived X ⥤
      ModuleDerived.Tensor.globalSectionsDerived X :=
  (ModuleDerived.Tensor.globalSectionsCurried X).obj ((globalDerived X).obj K)

/-- The image of the source Mayer--Vietoris triangle under the fixed-factor tensor functor. -/
@[stacks 0G6X "mapped source Mayer--Vietoris triangle"]
abbrev mappedSourceTriangle (X : RingedSpace.{u}) [ModuleDerived.Tensor.Has X]
    (U V : Opens X.carrier) (K M : ModuleDerived X)
    (δ : derived X (U ⊓ V) ⟶ globalDerived X ⋙
      shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ))
    [CategoryTheory.Functor.CommShift (tensorFunctor X K) ℤ] :
    Triangle (ModuleDerived.Tensor.globalSectionsDerived X) :=
  (tensorFunctor X K).mapTriangle.obj (sourceTriangle X U V M δ)

/-- Data expressing exactly the coherence needed for the three cup-product components to form a
Mayer--Vietoris triangle morphism.  The objectwise `TensorModel` comparisons alone do not imply
these fields; applications should obtain them from their restriction/naturality API. -/
@[stacks 0G6X "Mayer--Vietoris cup-product compatibility"]
structure Compatibility [ModuleDerived.Tensor.Has X]
    (global : GlobalTensorModel X) (U V : Opens X.carrier)
    (P_U : TensorModel X U) (P_V : TensorModel X V)
    (P_UV : TensorModel X (U ⊓ V)) (hUV : U ⊔ V = ⊤)
    (K M : ModuleDerived X)
    [CategoryTheory.Functor.CommShift (tensorFunctor X K) ℤ] where
  /-- The connecting map for the source Mayer--Vietoris triangle. -/
  δ : derived X (U ⊓ V) ⟶ globalDerived X ⋙
    shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)
  /-- The connecting map for the target tensor Mayer--Vietoris triangle. -/
  δ' : derived X (U ⊓ V) ⟶ globalDerived X ⋙
    shiftFunctor (ModuleDerived.Tensor.globalSectionsDerived X) (1 : ℤ)
  /-- The source Mayer--Vietoris triangle is distinguished. -/
  source_distinguished :
    sourceTriangle X U V M δ ∈ distTriang (ModuleDerived.Tensor.globalSectionsDerived X)
  /-- The target Mayer--Vietoris triangle is distinguished. -/
  target_distinguished :
    targetTriangle X U V K M δ' ∈ distTriang (ModuleDerived.Tensor.globalSectionsDerived X)
  /-- The first square of the cup-product triangle morphism commutes. -/
  comm₁ :
    (mappedSourceTriangle X U V K M δ).mor₁ ≫
        biprodComponent U V P_U P_V K M δ δ' =
      globalComponent global U V K M δ δ' ≫
        (targetTriangle X U V K M δ').mor₁
  /-- The second square of the cup-product triangle morphism commutes. -/
  comm₂ :
    (mappedSourceTriangle X U V K M δ).mor₂ ≫
        overlapComponent P_UV K M δ δ' =
      biprodComponent U V P_U P_V K M δ δ' ≫
        (targetTriangle X U V K M δ').mor₂
  /-- The shifted third square of the cup-product triangle morphism commutes. -/
  comm₃ :
    (mappedSourceTriangle X U V K M δ).mor₃ ≫
        (globalComponent global U V K M δ δ')⟦(1 : ℤ)⟧' =
      overlapComponent P_UV K M δ δ' ≫
        (targetTriangle X U V K M δ').mor₃

/-- The triangle morphism determined by Mayer--Vietoris compatibility data. -/
@[stacks 0G6X "cup-product triangle morphism from compatibility data"]
noncomputable def triangleMorphism [ModuleDerived.Tensor.Has X]
    (global : GlobalTensorModel X) (U V : Opens X.carrier)
    (P_U : TensorModel X U) (P_V : TensorModel X V) (P_UV : TensorModel X (U ⊓ V))
    (hUV : U ⊔ V = ⊤) (K M : ModuleDerived X)
    [CategoryTheory.Functor.CommShift (tensorFunctor X K) ℤ]
    (h : Compatibility global U V P_U P_V P_UV hUV K M) :
    mappedSourceTriangle X U V K M h.δ ⟶ targetTriangle X U V K M h.δ' :=
  Triangle.homMk _ _
    (globalComponent global U V K M h.δ h.δ')
    (biprodComponent U V P_U P_V K M h.δ h.δ')
    (overlapComponent P_UV K M h.δ h.δ')
    h.comm₁ h.comm₂ h.comm₃

/-- Cup products assemble into a morphism from the tensor of the derived-sections
Mayer--Vietoris triangle to the triangle of the tensor product, once the restriction/naturality
compatibility data has been supplied. -/
@[stacks 0G6X "cup product on Mayer--Vietoris triangles"]
theorem mayerVietorisTriangleMorphism [ModuleDerived.Tensor.Has X]
    (global : GlobalTensorModel X) (U V : Opens X.carrier)
    (P_U : TensorModel X U) (P_V : TensorModel X V) (P_UV : TensorModel X (U ⊓ V))
    (hUV : U ⊔ V = ⊤) (K M : ModuleDerived X)
    [CategoryTheory.Functor.CommShift (tensorFunctor X K) ℤ]
    (h : Compatibility global U V P_U P_V P_UV hUV K M) :
    sourceTriangle X U V M h.δ ∈ distTriang (ModuleDerived.Tensor.globalSectionsDerived X) ∧
      targetTriangle X U V K M h.δ' ∈ distTriang (ModuleDerived.Tensor.globalSectionsDerived X) ∧
      ∃ φ : mappedSourceTriangle X U V K M h.δ ⟶ targetTriangle X U V K M h.δ',
        φ.hom₁ = globalComponent global U V K M h.δ h.δ' ∧
          φ.hom₂ = biprodComponent U V P_U P_V K M h.δ h.δ' ∧
            φ.hom₃ = overlapComponent P_UV K M h.δ h.δ' := sorry

end MayerVietoris

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

end
