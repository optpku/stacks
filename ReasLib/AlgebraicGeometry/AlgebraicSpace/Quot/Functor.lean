/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
quasi-coherent module on an algebraic space, identified by kernels. The common
representative data and pullback are defined for algebraic-space test objects;
scheme points retain a thin facade for their specialized pullback API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The pullback `F_T` of a module `F` along the projection `X ×_{B,h} T ⟶ X`. -/
def spaceFiberF {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) :
    (pullback f h).Modules :=
  (Modules.pullback (pullback.fst f h)).obj F

/-- The canonical map `X_{T'} ⟶ X_T` induced by a morphism over `B` with its commutativity equality. -/
def spaceFiberMapOver (f : X ⟶ B) {T T' : AlgebraicSpace S} {h : T ⟶ B} {h' : T' ⟶ B}
    (a : T' ⟶ T) (w : a ≫ h = h') :
    pullback f h' ⟶ pullback f h :=
  pullback.map f h' f h (𝟙 X) a (𝟙 B)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id h').trans w.symm)

/-- The map of fibers over `B` preserves the projection to `X`. -/
@[simp]
theorem spaceFiberMapOver_fst (f : X ⟶ B) {T T' : AlgebraicSpace S}
    {h : T ⟶ B} {h' : T' ⟶ B} (a : T' ⟶ T) (w : a ≫ h = h') :
    spaceFiberMapOver f a w ≫ pullback.fst f h = pullback.fst f h' := by
  unfold spaceFiberMapOver pullback.map
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The map of fibers over `B` preserves the projection to the test space. -/
@[simp]
theorem spaceFiberMapOver_snd (f : X ⟶ B) {T T' : AlgebraicSpace S}
    {h : T ⟶ B} {h' : T' ⟶ B} (a : T' ⟶ T) (w : a ≫ h = h') :
    spaceFiberMapOver f a w ≫ pullback.snd f h = pullback.snd f h' ≫ a := by
  unfold spaceFiberMapOver pullback.map
  exact pullback.lift_snd _ _ _

/-- The comparison identifying `F_{T'}` with the pullback of `F_T` along `X_{T'} ⟶ X_T`. -/
def spaceFiberFOverIso (f : X ⟶ B) (F : X.Modules) {T T' : AlgebraicSpace S}
    {h : T ⟶ B} {h' : T' ⟶ B} (a : T' ⟶ T) (w : a ≫ h = h') :
    spaceFiberF f F h' ≅ (Modules.pullback (spaceFiberMapOver f a w)).obj (spaceFiberF f F h) :=
  eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
      ((pullback.lift_fst (pullback.fst f h' ≫ 𝟙 X)
          (pullback.snd f h' ≫ a)
          (((Category.assoc (pullback.fst f h') (𝟙 X) f).trans
              (congrArg (fun k ↦ pullback.fst f h' ≫ k) (Category.id_comp f))).trans
            ((pullback.condition :
                pullback.fst f h' ≫ f = pullback.snd f h' ≫ h').trans
              ((congrArg (fun k ↦ pullback.snd f h' ≫ k)
                  w.symm).trans
                (Category.assoc (pullback.snd f h')
                  a h).symm)))).trans
        (Category.comp_id _)).symm) ≪≫
    (Modules.pullbackCompIso (spaceFiberMapOver f a w) (pullback.fst f h)).symm.app F

/-- The canonical map of fibers along a morphism of test algebraic spaces. -/
def spaceFiberMap {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B) (a : T' ⟶ T) :
    pullback f (a ≫ h) ⟶ pullback f h :=
  spaceFiberMapOver f a rfl

/-- The map `spaceFiberMap f h a` commutes with the projections to `X`. -/
theorem spaceFiberMap_fst {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) :
    spaceFiberMap f h a ≫ pullback.fst f h = pullback.fst f (a ≫ h) :=
  spaceFiberMapOver_fst f a rfl

/-- The map `spaceFiberMap f h a` commutes with the projections to the varying base. -/
theorem spaceFiberMap_snd {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) :
    spaceFiberMap f h a ≫ pullback.snd f h = pullback.snd f (a ≫ h) ≫ a :=
  spaceFiberMapOver_snd f a rfl

/-- Pullback comparison for the source module over test algebraic spaces. -/
def spaceFiberFCompIso {T T' : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) (a : T' ⟶ T) :
    spaceFiberF f F (a ≫ h) ≅
      (Modules.pullback (spaceFiberMap f h a)).obj (spaceFiberF f F h) :=
  spaceFiberFOverIso f F a rfl

/-- A quasi-coherent quotient of `F_T` that is flat over an algebraic space `T`. -/
structure SpacePoint {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) where
  /-- The target module sheaf of the quotient. -/
  module : (pullback f h).Modules
  /-- The quotient morphism from `F_T`. -/
  map : spaceFiberF f F h ⟶ module
  /-- The quotient morphism is an epimorphism. -/
  map_epi : Epi map
  /-- The target is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The target is flat over `T`. -/
  isFlat : Modules.flatOver module (pullback.snd f h)

namespace SpacePoint

/-- Construct a space-level quotient point from an epimorphism `F_T ⟶ Q` with `Q`
quasi-coherent and flat over `T`. -/
def ofEpi {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B)
    (module : (pullback f h).Modules) (map : spaceFiberF f F h ⟶ module)
    (map_epi : Epi map) (isQuasicoherent : module.IsQuasicoherent)
    (isFlat : Modules.flatOver module (pullback.snd f h)) : SpacePoint f F h where
  module := module
  map := map
  map_epi := map_epi
  isQuasicoherent := isQuasicoherent
  isFlat := isFlat

/-- A space-level quotient point is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent
and flat over `T`. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : SpacePoint f F h) :
    Epi Q.map ∧ Q.module.IsQuasicoherent ∧
      Modules.flatOver Q.module (pullback.snd f h) := sorry

/-- Base change preserves epimorphy, quasi-coherence and relative flatness. -/
theorem pullbackOver_properties {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} {h' : T' ⟶ B} (Q : SpacePoint f F h)
    (a : T' ⟶ T) (w : a ≫ h = h') :
    Epi ((spaceFiberFOverIso f F a w).hom ≫
      (Modules.pullback (spaceFiberMapOver f a w)).map Q.map) ∧
    ((Modules.pullback (spaceFiberMapOver f a w)).obj Q.module).IsQuasicoherent ∧
    Modules.flatOver ((Modules.pullback (spaceFiberMapOver f a w)).obj Q.module)
      (pullback.snd f h') := sorry

/-- Pull back along a map over `B`, retaining the specified target structure map. -/
def pullbackOver {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} {h' : T' ⟶ B} (Q : SpacePoint f F h)
    (a : T' ⟶ T) (w : a ≫ h = h') : SpacePoint f F h' where
  module := (Modules.pullback (spaceFiberMapOver f a w)).obj Q.module
  map := (spaceFiberFOverIso f F a w).hom ≫
    (Modules.pullback (spaceFiberMapOver f a w)).map Q.map
  map_epi := (pullbackOver_properties Q a w).1
  isQuasicoherent := (pullbackOver_properties Q a w).2.1
  isFlat := (pullbackOver_properties Q a w).2.2

set_option maxHeartbeats 1000000 in
/-- Pulling back a quotient preserves epimorphy, quasi-coherence and flatness. -/
theorem pullback_properties {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} (Q : SpacePoint f F h) (a : T' ⟶ T) :
    Epi ((spaceFiberFCompIso f F h a).hom ≫
      (Modules.pullback (spaceFiberMap f h a)).map Q.map) ∧
    ((Modules.pullback (spaceFiberMap f h a)).obj Q.module).IsQuasicoherent ∧
    Modules.flatOver ((Modules.pullback (spaceFiberMap f h a)).obj Q.module)
      (pullback.snd f (a ≫ h)) := pullbackOver_properties Q a rfl

/-- Pull back a space-level quotient point along a morphism of algebraic spaces. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : SpacePoint f F h) (a : T' ⟶ T) : SpacePoint f F (a ≫ h) :=
  Q.pullbackOver a rfl

/-- The module of a pulled-back space-level point is the module pullback along
`spaceFiberMap`. -/
theorem pullback_module {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} (Q : SpacePoint f F h) (a : T' ⟶ T) :
    (Q.pullback a).module = (Modules.pullback (spaceFiberMap f h a)).obj Q.module := rfl

/-- Two space-level quotient points are identified when they have the same kernel. -/
def Rel {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q₁ Q₂ : SpacePoint f F h) : Prop :=
  kernelSubobject Q₁.map = kernelSubobject Q₂.map

/-- Kernel equality is an equivalence relation on space-level quotient points. -/
theorem rel_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) : Equivalence (fun Q₁ Q₂ : SpacePoint f F h ↦ Rel Q₁ Q₂) := sorry

/-- Kernel identification of space-level quotient points is equivalent to an isomorphism
of targets over `F_T`. -/
theorem rel_iso_iff {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q₁ Q₂ : SpacePoint f F h) :
    Rel Q₁ Q₂ ↔ ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map := sorry

set_option maxHeartbeats 1000000 in
/-- Base change over `B` preserves kernel identification, via the induced target isomorphism. -/
theorem rel_pullbackOver {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} {h' : T' ⟶ B} (Q R : SpacePoint f F h) (hQ : Rel Q R)
    (a : T' ⟶ T) (w : a ≫ h = h') : Rel (Q.pullbackOver a w) (R.pullbackOver a w) := by
  obtain ⟨e, he⟩ := (rel_iso_iff Q R).1 hQ
  refine (rel_iso_iff _ _).2 ⟨(Modules.pullback (spaceFiberMapOver f a w)).mapIso e, ?_⟩
  change ((spaceFiberFOverIso f F a w).hom ≫
    (Modules.pullback (spaceFiberMapOver f a w)).map Q.map) ≫
      (Modules.pullback (spaceFiberMapOver f a w)).map e.hom =
    (spaceFiberFOverIso f F a w).hom ≫
      (Modules.pullback (spaceFiberMapOver f a w)).map R.map
  rw [Category.assoc, ← Functor.map_comp, he]

end SpacePoint

/-- The base change `X_T = X ×_B T` of `X` along a scheme `T` over `B`. -/
def fiber (f : X ⟶ B) (σ : SchemeOver B) : AlgebraicSpace S :=
  pullback f σ.hom

/-- The pullback `F_T` of a module `F` along the projection `X_T ⟶ X`. -/
def fiberF (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) : (fiber f σ).Modules :=
  (Modules.pullback (pullback.fst f σ.hom)).obj F

/-- The map of fibers induced by a morphism of test schemes over `B`. -/
def fiberMap (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiber f τ ⟶ fiber f σ :=
  spaceFiberMapOver f ((ofOverFunctor S).map h.left) (CostructuredArrow.w h)

/-- The map `fiberMap f h` commutes with the projections to `X`. -/
theorem fiberMap_fst (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiberMap f h ≫ pullback.fst f σ.hom = pullback.fst f τ.hom :=
  spaceFiberMapOver_fst f _ (CostructuredArrow.w h)

/-- The map `fiberMap f h` commutes with the projections to the varying base. -/
theorem fiberMap_snd (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiberMap f h ≫ pullback.snd f σ.hom =
      pullback.snd f τ.hom ≫ (ofOverFunctor S).map h.left :=
  spaceFiberMapOver_snd f _ (CostructuredArrow.w h)

/-- The source-module comparison for a morphism of test schemes over `B`. -/
def fiberFCompIso (f : X ⟶ B) (F : X.Modules) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiberF f F τ ≅ (Modules.pullback (fiberMap f h)).obj (fiberF f F σ) :=
  spaceFiberFOverIso f F ((ofOverFunctor S).map h.left) (CostructuredArrow.w h)

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

/-- View a scheme-level quotient point as a space-level quotient point along `σ.hom`. -/
def Point.toSpacePoint {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (Q : Point f F σ) : SpacePoint f F σ.hom where
  module := Q.module
  map := Q.map
  map_epi := Q.map_epi
  isQuasicoherent := Q.isQuasicoherent
  isFlat := Q.isFlat

/-- Repackage a common quotient over a scheme, preserving its module and quotient map.
The specialized record retains the original scheme projections and constructor API. -/
def Point.ofSpacePoint {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (Q : SpacePoint f F σ.hom) : Point f F σ where
  module := Q.module
  map := Q.map
  map_epi := Q.map_epi
  isQuasicoherent := Q.isQuasicoherent
  isFlat := Q.isFlat

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
  map_epi := by
    change Epi (cokernel.π kernel.arrow)
    infer_instance
  isQuasicoherent := isQuasicoherent
  isFlat := isFlat

/-- A quotient point is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent and flat over `T`. -/
theorem spec {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} (Q : Point f F σ) :
    Epi Q.map ∧ Q.module.IsQuasicoherent ∧
      Modules.flatOver Q.module (pullback.snd f σ.hom) := sorry

set_option maxHeartbeats 1000000 in
/-- The pulled-back quotient map is an epimorphism, and its target is quasi-coherent
and flat over the new base scheme. -/
theorem pullback_properties {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : Point f F σ) (h : τ ⟶ σ) :
    Epi ((fiberFCompIso f F h).hom ≫ (Modules.pullback (fiberMap f h)).map Q.map) ∧
      ((Modules.pullback (fiberMap f h)).obj Q.module).IsQuasicoherent ∧
      Modules.flatOver ((Modules.pullback (fiberMap f h)).obj Q.module)
        (pullback.snd f τ.hom) :=
  SpacePoint.pullbackOver_properties Q.toSpacePoint _ (CostructuredArrow.w h)

/-- Pull back a quotient point along a morphism of schemes over `B`. -/
def pullback {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B} (Q : Point f F σ)
    (h : τ ⟶ σ) : Point f F τ :=
  ofSpacePoint (SpacePoint.pullbackOver Q.toSpacePoint ((ofOverFunctor S).map h.left)
    (CostructuredArrow.w h))

/-- The module of a pulled-back point is the module pullback along `fiberMap`. -/
theorem pullback_module {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : Point f F σ) (h : τ ⟶ σ) :
    (Q.pullback h).module = (Modules.pullback (fiberMap f h)).obj Q.module := rfl

end Point

/-- Two quotient points are identified when they have the same kernel. -/
def Rel {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} (Q₁ Q₂ : Point f F σ) : Prop :=
  SpacePoint.Rel Q₁.toSpacePoint Q₂.toSpacePoint

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

set_option maxHeartbeats 1000000 in
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
