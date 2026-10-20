/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation
public import ReasLib.CategoryTheory.Linear.Functor

/-!
# Obstruction theories for categories fibred in groupoids

An obstruction theory on a category fibred in groupoids over `(Sch/S)_fppf`
is additional data: `A`-linear functors of obstruction modules, functoriality
maps along change of rings/modules/restriction, and obstruction classes for
deformation situations, subject to functoriality, naturality, and the lifting
criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- A triple `(x, A, M)` consisting of an object over `Spec(A) → S` and an
`A`-module. -/
structure ObstructionTriple (X : GroupoidsOver S) extends ObjectOverSpec X where
  /-- The `A`-module `M`. -/
  M : ModuleCat.{u} toCommRingCat

namespace ObstructionTriple

variable {X : GroupoidsOver S}

/-- Package an object over `Spec(A)` with an `A`-module as an obstruction
triple. -/
def of (ξ : ObjectOverSpec X) (M : ModuleCat.{u} ξ.carrier) : ObstructionTriple X where
  toObjectOverSpec := ξ
  M := M

/-- An obstruction triple is an object over `Spec(A)` together with an
`A`-module. -/
theorem spec (ξ : ObstructionTriple X) :
    ξ.toS.MapsIntoAffineOpen ∧ X.p.obj ξ.obj = Over.mk ξ.toS :=
  sorry

/-- A morphism of triples along `A → B`: a morphism of objects over spectra
together with an `A`-linear map `M → N` after restriction of scalars. -/
structure Hom (ξ η : ObstructionTriple X)
    extends ObjectOverSpec.Hom ξ.toObjectOverSpec η.toObjectOverSpec where
  /-- The `A`-linear map `M → N` after restriction of scalars along `A → B`. -/
  toModule : ξ.M ⟶ (ModuleCat.restrictScalars toRingHom).obj η.M

/-- Package a morphism of objects over spectra and an `A`-linear module map as
a morphism of obstruction triples. -/
def Hom.of {ξ η : ObstructionTriple X}
    (toHom : ObjectOverSpec.Hom ξ.toObjectOverSpec η.toObjectOverSpec)
    (toModule : ξ.M ⟶ (ModuleCat.restrictScalars toHom.toRingHom).obj η.M) :
    Hom ξ η where
  toHom := toHom
  toModule := toModule

/-- A morphism of triples is a ring map `A → B`, a restriction arrow `y ⟶ x`,
and an `A`-linear map of modules after restriction of scalars. -/
theorem Hom.spec {ξ η : ObstructionTriple X} (f : Hom ξ η) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ξ.toS = η.toS ∧
      X.p.IsHomLift (ObjectOverSpec.specOverMap f.toRingHom f.toS_comp) f.restriction :=
  sorry

/-- Identity morphism of an obstruction triple. -/
def Hom.id (ξ : ObstructionTriple X) : Hom ξ ξ where
  toHom := ObjectOverSpec.Hom.id ξ.toObjectOverSpec
  toModule := (ModuleCat.restrictScalarsId ξ.carrier).inv.app ξ.M

/-- Composition of morphisms of obstruction triples. -/
def Hom.comp {ξ η ζ : ObstructionTriple X} (f : Hom ξ η) (g : Hom η ζ) : Hom ξ ζ where
  toHom := ObjectOverSpec.Hom.comp f.toHom g.toHom
  toModule :=
    f.toModule ≫ (ModuleCat.restrictScalars f.toRingHom).map g.toModule ≫
      (ModuleCat.restrictScalarsComp' f.toRingHom g.toRingHom
        (g.toRingHom.comp f.toRingHom) rfl).inv.app ζ.M

/-- A module morphism over a fixed object defines a morphism of obstruction triples. -/
def Hom.ofModuleHom (ξ : ObjectOverSpec X) {M N : ModuleCat.{u} ξ.carrier}
    (f : M ⟶ N) : Hom (ObstructionTriple.of ξ M) (ObstructionTriple.of ξ N) :=
  Hom.of (ObjectOverSpec.Hom.id ξ)
    (f ≫ (ModuleCat.restrictScalarsId ξ.carrier).inv.app N)

end ObstructionTriple

namespace DeformationSituation

variable {X : GroupoidsOver S}

/-- The obstruction triple `(x, A, I)` of a deformation situation, with
`I = Ker(A' → A)`. -/
def toTriple (σ : DeformationSituation X) : ObstructionTriple X :=
  ObstructionTriple.of σ.toObjectOverSpec σ.kernelModule

/-- `toTriple` is the object over `Spec(A)` paired with the kernel module. -/
theorem toTriple_M (σ : DeformationSituation X) :
    σ.toTriple.M = σ.kernelModule :=
  sorry

/-- The morphism of obstruction triples induced by a morphism of deformation
situations, using the kernel map on modules. -/
def Hom.toTripleHom {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ) :
    ObstructionTriple.Hom σ.toTriple τ.toTriple :=
  ObstructionTriple.Hom.of f.toHom f.kernelMap

/-- `toTripleHom` uses the stored restriction arrow and the kernel map. -/
theorem Hom.toTripleHom_toModule {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ) :
    (Hom.toTripleHom f).toModule = f.kernelMap :=
  sorry

end DeformationSituation

/-- An obstruction theory on a category fibred in groupoids over a locally
Noetherian base: functors of obstruction modules, functoriality maps, and
obstruction classes for deformation situations. -/
structure ObstructionTheory {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S) where
  /-- The `A`-linear functor `O_x : Mod_A ⥤ Mod_A` of obstruction modules. -/
  module : (ξ : ObjectOverSpec X) → ModuleCat.{u} ξ.carrier ⥤ ModuleCat.{u} ξ.carrier
  /-- Each `O_x` is additive and `A`-linear. -/
  moduleLinear : ∀ ξ, (module ξ).ModuleLinear ξ.carrier
  /-- Functoriality map `O_x(M) → O_y(N)` along a morphism of triples. -/
  map : {ξ η : ObstructionTriple X} → (f : ObstructionTriple.Hom ξ η) →
    (module ξ.toObjectOverSpec).obj ξ.M ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj ((module η.toObjectOverSpec).obj η.M)
  /-- Obstruction class `o_x(A') ∈ O_x(I)` of a deformation situation. -/
  obstruction : (σ : DeformationSituation X) →
    (module σ.toObjectOverSpec).obj σ.kernelModule
  /-- Identity morphisms of triples act as identity on obstruction modules,
  after identifying restriction of scalars along `id`. -/
  map_id : ∀ ξ : ObstructionTriple X,
    map (ObstructionTriple.Hom.id ξ) =
      (ModuleCat.restrictScalarsId ξ.carrier).inv.app
        ((module ξ.toObjectOverSpec).obj ξ.M)
  /-- Functoriality maps are compatible with composition of morphisms of
  triples. -/
  map_comp : ∀ {ξ η ζ : ObstructionTriple X} (f : ObstructionTriple.Hom ξ η)
      (g : ObstructionTriple.Hom η ζ),
    map (ObstructionTriple.Hom.comp f g) =
      map f ≫ (ModuleCat.restrictScalars f.toRingHom).map (map g) ≫
        (ModuleCat.restrictScalarsComp' f.toRingHom g.toRingHom
          (g.toRingHom.comp f.toRingHom) rfl).inv.app
          ((module ζ.toObjectOverSpec).obj ζ.M)
  /-- On module maps over a fixed object, the triple action agrees with its module functor. -/
  map_module : ∀ (ξ : ObjectOverSpec X) {M N : ModuleCat.{u} ξ.carrier} (f : M ⟶ N),
    map (ObstructionTriple.Hom.ofModuleHom ξ f) =
      (module ξ).map f ≫
        (ModuleCat.restrictScalarsId ξ.carrier).inv.app ((module ξ).obj N)
  /-- Obstruction classes are natural along morphisms of deformation
  situations. -/
  map_obstruction : ∀ {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ),
    map f.toTripleHom (obstruction σ) = obstruction τ
  /-- Lifts of `x` to `Spec(A')` exist if and only if the obstruction vanishes. -/
  lifts_iff : ∀ σ : DeformationSituation X,
    Nonempty (DeformationSituation.ObjectLift σ) ↔ obstruction σ = 0

namespace ObstructionTheory

variable {X : GroupoidsOver S}

/-- An obstruction theory supplies `A`-linear obstruction modules, functoriality
maps, natural obstruction classes, and the lifting criterion. -/
theorem spec (𝒪 : ObstructionTheory X) :
    (∀ ξ : ObjectOverSpec X, (𝒪.module ξ).ModuleLinear ξ.carrier) ∧
      (∀ ξ : ObstructionTriple X,
        𝒪.map (ObstructionTriple.Hom.id ξ) =
          (ModuleCat.restrictScalarsId ξ.carrier).inv.app
            ((𝒪.module ξ.toObjectOverSpec).obj ξ.M)) ∧
      (∀ {ξ η ζ : ObstructionTriple X} (f : ObstructionTriple.Hom ξ η)
          (g : ObstructionTriple.Hom η ζ),
        𝒪.map (ObstructionTriple.Hom.comp f g) =
          𝒪.map f ≫ (ModuleCat.restrictScalars f.toRingHom).map (𝒪.map g) ≫
            (ModuleCat.restrictScalarsComp' f.toRingHom g.toRingHom
              (g.toRingHom.comp f.toRingHom) rfl).inv.app
              ((𝒪.module ζ.toObjectOverSpec).obj ζ.M)) ∧
      (∀ (ξ : ObjectOverSpec X) {M N : ModuleCat.{u} ξ.carrier} (f : M ⟶ N),
        𝒪.map (ObstructionTriple.Hom.ofModuleHom ξ f) =
          (𝒪.module ξ).map f ≫
            (ModuleCat.restrictScalarsId ξ.carrier).inv.app ((𝒪.module ξ).obj N)) ∧
      (∀ {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ),
        𝒪.map f.toTripleHom (𝒪.obstruction σ) = 𝒪.obstruction τ) ∧
      ∀ σ : DeformationSituation X,
        Nonempty (DeformationSituation.ObjectLift σ) ↔ 𝒪.obstruction σ = 0 :=
  sorry

/-- The obstruction module `O_x(M)` of a triple `(x, A, M)`. -/
def moduleObj (𝒪 : ObstructionTheory X) (ξ : ObstructionTriple X) :
    ModuleCat.{u} ξ.carrier :=
  (𝒪.module ξ.toObjectOverSpec).obj ξ.M

/-- `moduleObj` is the value of the obstruction-module functor on `M`. -/
theorem module_apply (𝒪 : ObstructionTheory X) (ξ : ObstructionTriple X) :
    𝒪.moduleObj ξ = (𝒪.module ξ.toObjectOverSpec).obj ξ.M :=
  sorry

/-- Applying a functoriality map to an element of an obstruction module. -/
theorem map_apply (𝒪 : ObstructionTheory X) {ξ η : ObstructionTriple X}
    (f : ObstructionTriple.Hom ξ η) (m : (𝒪.module ξ.toObjectOverSpec).obj ξ.M) :
    𝒪.map f m = (𝒪.map f).hom m :=
  sorry

/-- The obstruction of a deformation situation vanishes if and only if there is
a lift of `x` along `Spec(A) ⟶ Spec(A')`. -/
theorem obstruction_eq_zero_iff_nonempty_objectLift (𝒪 : ObstructionTheory X)
    (σ : DeformationSituation X) :
    𝒪.obstruction σ = 0 ↔ Nonempty (DeformationSituation.ObjectLift σ) :=
  sorry

end ObstructionTheory

end AlgebraicGeometry.GroupoidsOver
