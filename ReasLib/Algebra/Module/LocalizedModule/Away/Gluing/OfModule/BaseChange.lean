module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.OfModule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change of the Gluing Attached to a Global Module

This leaf compares the two canonical ways to obtain target-side
principal-open gluing from a source module: extend the module first, or form
its source gluing first and then base-change that gluing.

@stack 05EL
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

noncomputable section

namespace LocalizedModule.Away.Gluing

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type w}

/-- The local comparison between localization of an extended global module
and the corresponding local piece in the base-changed source gluing. -/
@[stacks 05EQ "global-module gluing local base-change comparison",
  stacks 05EL "global-module gluing local base-change comparison"]
noncomputable def ofModuleBaseChangeLocalIso (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) (i : ι) :
    (ofModule (fun j ↦ φ (f j))
      ((ModuleCat.extendScalars φ).obj M)).localModule i ≅
      ((ofModule f M).baseChange φ).localModule i :=
  LocalizedModule.Away.baseChangeIso φ (f i) M ≪≫
    ((ofModule f M).toPreGluing.baseChangeLocalModuleIso φ i).symm

/-- The local comparison maps commute with the canonical pairwise overlap
isomorphisms. -/
@[stacks 05EL "global-module gluing base-change overlap naturality"]
theorem ofModuleBaseChangeHom_comm (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (φ (f i) * φ (f j)))
          ((ofModuleBaseChangeLocalIso φ f M i).hom.hom.restrictScalars S))
        ((ofModule (fun k ↦ φ (f k))
          ((ModuleCat.extendScalars φ).obj M)).overlapIso i j).hom
        (((ofModule f M).baseChange φ).overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (φ (f i) * φ (f j)))
          ((ofModuleBaseChangeLocalIso φ f M j).hom.hom.restrictScalars S)) := sorry

/-- The forward morphism comparing gluing after module base change with base
change of the source gluing. -/
@[stacks 05EL "global-module gluing base-change comparison morphism"]
noncomputable def ofModuleBaseChangeHom (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ofModule (fun i ↦ φ (f i)) ((ModuleCat.extendScalars φ).obj M) ⟶
      (ofModule f M).baseChange φ where
  hom i := (ofModuleBaseChangeLocalIso φ f M i).hom
  comm := ofModuleBaseChangeHom_comm φ f M

/-- The inverse local comparison maps also commute with the canonical
pairwise overlap isomorphisms. -/
@[stacks 05EL "inverse global-module gluing base-change overlap naturality"]
theorem ofModuleBaseChangeInv_comm (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (φ (f i) * φ (f j)))
          ((ofModuleBaseChangeLocalIso φ f M i).inv.hom.restrictScalars S))
        (((ofModule f M).baseChange φ).overlapIso i j).hom
        ((ofModule (fun k ↦ φ (f k))
          ((ModuleCat.extendScalars φ).obj M)).overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (φ (f i) * φ (f j)))
          ((ofModuleBaseChangeLocalIso φ f M j).inv.hom.restrictScalars S)) := sorry

/-- The inverse morphism of the global-module gluing base-change
comparison. -/
@[stacks 05EL "inverse global-module gluing base-change comparison morphism"]
noncomputable def ofModuleBaseChangeInv (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    (ofModule f M).baseChange φ ⟶
      ofModule (fun i ↦ φ (f i)) ((ModuleCat.extendScalars φ).obj M) where
  hom i := (ofModuleBaseChangeLocalIso φ f M i).inv
  comm := ofModuleBaseChangeInv_comm φ f M

/-- The forward and inverse comparison morphisms compose to the identity on
the gluing obtained from the extended global module. -/
@[stacks 05EL "global-module gluing base-change comparison hom-inv"]
theorem ofModuleBaseChange_hom_inv_id (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ofModuleBaseChangeHom φ f M ≫ ofModuleBaseChangeInv φ f M =
      𝟙 (ofModule (fun i ↦ φ (f i))
        ((ModuleCat.extendScalars φ).obj M)) := sorry

/-- The inverse and forward comparison morphisms compose to the identity on
the base-changed source gluing. -/
@[stacks 05EL "global-module gluing base-change comparison inv-hom"]
theorem ofModuleBaseChange_inv_hom_id (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ofModuleBaseChangeInv φ f M ≫ ofModuleBaseChangeHom φ f M =
      𝟙 ((ofModule f M).baseChange φ) := sorry

/-- Canonical isomorphism between gluing after module base change and base
change of the gluing attached to the source module. -/
@[stacks 05EL "global-module gluing commutes with base change"]
noncomputable def ofModuleBaseChangeIso (φ : R →+* S)
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ofModule (fun i ↦ φ (f i)) ((ModuleCat.extendScalars φ).obj M) ≅
      (ofModule f M).baseChange φ where
  hom := ofModuleBaseChangeHom φ f M
  inv := ofModuleBaseChangeInv φ f M
  hom_inv_id := ofModuleBaseChange_hom_inv_id φ f M
  inv_hom_id := ofModuleBaseChange_inv_hom_id φ f M

/-- The functor that first extends a module along `φ` and then forms its
target principal-open gluing. -/
@[stacks 05EL "extend module then form principal-open gluing"]
noncomputable def ofModuleAfterBaseChangeFunctor (φ : R →+* S)
    (f : ι → R) :
    ModuleCat.{max u v} R ⥤ Gluing (fun i ↦ φ (f i)) :=
  ModuleCat.extendScalars φ ⋙ ofModuleFunctor (fun i ↦ φ (f i))

/-- The functor that first forms source principal-open gluing and then
base-changes that gluing along `φ`. -/
@[stacks 05EL "form principal-open gluing then base change"]
noncomputable def baseChangeAfterOfModuleFunctor (φ : R →+* S)
    (f : ι → R) :
    ModuleCat.{max u v} R ⥤ Gluing (fun i ↦ φ (f i)) :=
  ofModuleFunctor f ⋙ baseChangeFunctor φ

/-- The objectwise gluing base-change comparisons are natural in the global
source module. -/
@[stacks 05EL "global-module gluing base-change naturality"]
theorem ofModuleBaseChange_naturality (φ : R →+* S)
    (f : ι → R) {M N : ModuleCat.{max u v} R} (ψ : M ⟶ N) :
    (ofModuleAfterBaseChangeFunctor φ f).map ψ ≫
        (ofModuleBaseChangeIso φ f N).hom =
      (ofModuleBaseChangeIso φ f M).hom ≫
        (baseChangeAfterOfModuleFunctor φ f).map ψ := sorry

/-- Forming the principal-open gluing of a module commutes naturally with
base change. -/
@[stacks 05EL "global-module gluing base-change natural isomorphism"]
noncomputable def ofModuleBaseChangeNatIso (φ : R →+* S)
    (f : ι → R) :
    ofModuleAfterBaseChangeFunctor φ f ≅
      baseChangeAfterOfModuleFunctor φ f :=
  NatIso.ofComponents (fun M ↦ ofModuleBaseChangeIso φ f M)
    (fun ψ ↦ ofModuleBaseChange_naturality φ f ψ)

end LocalizedModule.Away.Gluing
