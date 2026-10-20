module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# The functor of quotients of a quasi-coherent module

This module constructs the contravariant functor of quasi-coherent quotients of a
quasi-coherent module on an algebraic space, identified by kernels and required to be
flat over the test scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The base change `X_T = X ×_B T` of `X` along a scheme `T` over `B`. -/
def fiber (f : X ⟶ B) (σ : SchemeOver B) : AlgebraicSpace S :=
  pullback f σ.hom

/-- The pullback `F_T` of a module `F` along the projection `X_T ⟶ X`. -/
def fiberF (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) : (fiber f σ).Modules :=
  (Modules.pullback (pullback.fst f σ.hom)).obj F

/-- The canonical map `X_{T'} ⟶ X_T` induced by a morphism of schemes over `B`. -/
def fiberMap (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiber f τ ⟶ fiber f σ :=
  pullback.map f τ.hom f σ.hom (𝟙 X) ((ofOverFunctor S).map h.left) (𝟙 B)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id τ.hom).trans (CostructuredArrow.w h).symm)

/-- The map `fiberMap f h` commutes with the projections to `X`. -/
theorem fiberMap_fst (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiberMap f h ≫ pullback.fst f σ.hom = pullback.fst f τ.hom := sorry

/-- The map `fiberMap f h` commutes with the projections to the varying base. -/
theorem fiberMap_snd (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiberMap f h ≫ pullback.snd f σ.hom =
      pullback.snd f τ.hom ≫ (ofOverFunctor S).map h.left := sorry

/-- The comparison identifying `F_{T'}` with the pullback of `F_T` along `X_{T'} ⟶ X_T`. -/
def fiberFCompIso (f : X ⟶ B) (F : X.Modules) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiberF f F τ ≅ (Modules.pullback (fiberMap f h)).obj (fiberF f F σ) :=
  eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
      ((pullback.lift_fst (pullback.fst f τ.hom ≫ 𝟙 X)
          (pullback.snd f τ.hom ≫ (ofOverFunctor S).map h.left)
          (((Category.assoc (pullback.fst f τ.hom) (𝟙 X) f).trans
              (congrArg (fun k ↦ pullback.fst f τ.hom ≫ k) (Category.id_comp f))).trans
            ((pullback.condition :
                pullback.fst f τ.hom ≫ f = pullback.snd f τ.hom ≫ τ.hom).trans
              ((congrArg (fun k ↦ pullback.snd f τ.hom ≫ k)
                  (CostructuredArrow.w h).symm).trans
                (Category.assoc (pullback.snd f τ.hom)
                  ((ofOverFunctor S).map h.left) σ.hom).symm)))).trans
        (Category.comp_id _)).symm) ≪≫
    (Modules.pullbackCompIso (fiberMap f h) (pullback.fst f σ.hom)).symm.app F

/-- A quasi-coherent quotient of `F_T` that is flat over `T`. -/
structure Point (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) where
  /-- The target module sheaf of the quotient. -/
  module : (fiber f σ).Modules
  /-- The quotient morphism from `F_T`. -/
  map : fiberF f F σ ⟶ module
  /-- The quotient morphism is an epimorphism. -/
  map_epi : Epi map
  /-- The target is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The target is flat over `T`. -/
  isFlat : Modules.flatOver module (pullback.snd f σ.hom)

namespace Point

/-- Construct a quotient point from an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent and
flat over `T`. -/
def ofEpi (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B)
    (module : (fiber f σ).Modules) (map : fiberF f F σ ⟶ module)
    (map_epi : Epi map) (isQuasicoherent : module.IsQuasicoherent)
    (isFlat : Modules.flatOver module (pullback.snd f σ.hom)) : Point f F σ where
  module := module
  map := map
  map_epi := map_epi
  isQuasicoherent := isQuasicoherent
  isFlat := isFlat

/-- Construct a quotient point as the cokernel of a subobject of `F_T`. -/
def ofKernel (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B)
    (kernel : Subobject (fiberF f F σ))
    (isQuasicoherent : (cokernel kernel.arrow).IsQuasicoherent)
    (isFlat : Modules.flatOver (cokernel kernel.arrow) (pullback.snd f σ.hom)) :
    Point f F σ where
  module := cokernel kernel.arrow
  map := cokernel.π kernel.arrow
  map_epi := inferInstance
  isQuasicoherent := isQuasicoherent
  isFlat := isFlat

/-- A quotient point is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent and flat over `T`. -/
theorem spec {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} (Q : Point f F σ) :
    Epi Q.map ∧ Q.module.IsQuasicoherent ∧
      Modules.flatOver Q.module (pullback.snd f σ.hom) := sorry

/-- The pulled-back quotient map is an epimorphism, and its target is quasi-coherent
and flat over the new base scheme. -/
theorem pullback_properties {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : Point f F σ) (h : τ ⟶ σ) :
    Epi ((fiberFCompIso f F h).hom ≫ (Modules.pullback (fiberMap f h)).map Q.map) ∧
      ((Modules.pullback (fiberMap f h)).obj Q.module).IsQuasicoherent ∧
      Modules.flatOver ((Modules.pullback (fiberMap f h)).obj Q.module)
        (pullback.snd f τ.hom) := sorry

/-- Pull back a quotient point along a morphism of schemes over `B`. -/
def pullback {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B} (Q : Point f F σ)
    (h : τ ⟶ σ) : Point f F τ where
  module := (Modules.pullback (fiberMap f h)).obj Q.module
  map := (fiberFCompIso f F h).hom ≫ (Modules.pullback (fiberMap f h)).map Q.map
  map_epi := (pullback_properties Q h).1
  isQuasicoherent := (pullback_properties Q h).2.1
  isFlat := (pullback_properties Q h).2.2

/-- The module of a pulled-back point is the module pullback along `fiberMap`. -/
theorem pullback_module {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : Point f F σ) (h : τ ⟶ σ) :
    (Q.pullback h).module = (Modules.pullback (fiberMap f h)).obj Q.module := sorry

end Point

/-- Two quotient points are identified when they have the same kernel. -/
def Rel {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} (Q₁ Q₂ : Point f F σ) : Prop :=
  kernelSubobject Q₁.map = kernelSubobject Q₂.map

/-- Kernel equality is an equivalence relation on quotient points. -/
theorem rel_isEquivalence (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) :
    Equivalence (@Rel _ _ _ f F σ) := sorry

/-- Kernel identification of quotient points is equivalent to an isomorphism of
targets over `F_T`. -/
theorem rel_iso_iff {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} (Q₁ Q₂ : Point f F σ) :
    Rel Q₁ Q₂ ↔ ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map := sorry

/-- The setoid of quotient points modulo kernel equality. -/
def quotientSetoid (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) :
    Setoid (Point f F σ) where
  r := Rel
  iseqv := rel_isEquivalence f F σ

/-- Pullback preserves kernel identification of quotient points. -/
theorem rel_pullback (f : X ⟶ B) (F : X.Modules) {σ τ : SchemeOver B} (h : τ ⟶ σ)
    {Q₁ Q₂ : Point f F σ} (hQ : Rel Q₁ Q₂) :
    Rel (Q₁.pullback h) (Q₂.pullback h) := sorry

/-- Pullback along the identity is kernel-identified with the original quotient point. -/
theorem pullback_id_rel (f : X ⟶ B) (F : X.Modules) {σ : SchemeOver B} (Q : Point f F σ) :
    Rel (Q.pullback (𝟙 σ)) Q := sorry

/-- Pullback along a composite is kernel-identified with the iterated pullback. -/
theorem pullback_comp_rel (f : X ⟶ B) (F : X.Modules) {σ τ ρ : SchemeOver B}
    (h : τ ⟶ σ) (k : ρ ⟶ τ) (Q : Point f F σ) :
    Rel (Q.pullback (k ≫ h)) ((Q.pullback h).pullback k) := sorry

/-- Pullback preserves the relation of the quotient setoid. -/
theorem quotientSetoid_rel_pullback (f : X ⟶ B) (F : X.Modules) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) :
    ∀ (Q₁ Q₂ : Point f F σ),
      (quotientSetoid f F σ).r Q₁ Q₂ →
        (quotientSetoid f F τ).r (Q₁.pullback h) (Q₂.pullback h) := sorry

/-- Pullback along the identity induces the identity on kernel-identified quotient classes. -/
theorem functor_map_id (f : X ⟶ B) (F : X.Modules) (σ : (SchemeOver B)ᵒᵖ) :
    TypeCat.ofHom (_root_.Quotient.map (fun Q : Point f F σ.unop ↦ Q.pullback (𝟙 σ).unop)
        (quotientSetoid_rel_pullback f F (𝟙 σ).unop)) =
      𝟙 (_root_.Quotient (quotientSetoid f F σ.unop)) := sorry

/-- Pullback along a composite induces the composite of the pullback maps on quotient classes. -/
theorem functor_map_comp (f : X ⟶ B) (F : X.Modules) {σ τ ρ : (SchemeOver B)ᵒᵖ}
    (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    TypeCat.ofHom (_root_.Quotient.map (fun Q : Point f F σ.unop ↦ Q.pullback (h ≫ k).unop)
        (quotientSetoid_rel_pullback f F (h ≫ k).unop)) =
      TypeCat.ofHom (_root_.Quotient.map (fun Q : Point f F σ.unop ↦ Q.pullback h.unop)
          (quotientSetoid_rel_pullback f F h.unop)) ≫
        TypeCat.ofHom (_root_.Quotient.map (fun Q : Point f F τ.unop ↦ Q.pullback k.unop)
            (quotientSetoid_rel_pullback f F k.unop)) := sorry

/-- The contravariant functor of quasi-coherent quotients of `F` along `f : X ⟶ B`,
identified by kernels. -/
def functor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := _root_.Quotient (quotientSetoid f F σ.unop)
  map {σ τ} (h : σ ⟶ τ) :=
    TypeCat.ofHom (_root_.Quotient.map (fun Q : Point f F σ.unop ↦ Q.pullback h.unop)
      (quotientSetoid_rel_pullback f F h.unop))
  map_id := functor_map_id f F
  map_comp := functor_map_comp f F

/-- The value of the quotient functor is the setoid quotient of quotient points by kernels. -/
theorem functor_obj (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] (σ : SchemeOver B) :
    (functor f F).obj (op σ) = _root_.Quotient (quotientSetoid f F σ) := sorry

/-- The quotient functor acts on a morphism by pullback of quotient points. -/
theorem functor_map (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (functor f F).map h =
      TypeCat.ofHom (_root_.Quotient.map (fun Q : Point f F σ.unop ↦ Q.pullback h.unop)
        (quotientSetoid_rel_pullback f F h.unop)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
