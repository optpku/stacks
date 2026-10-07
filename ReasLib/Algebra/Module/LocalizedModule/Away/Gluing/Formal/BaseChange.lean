module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BaseChange.Square
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.OfModule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of formal principal-open gluing

A commutative square of ring maps sends formal gluing data over its upper
edge to formal gluing data over its lower edge.  The source-gluing comparison
uses the canonical composition and family-transport isomorphisms for
principal-open gluing.

@stack 05EQ
-/

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S Rp Sp : Type u}
variable [CommRing R] [CommRing S] [CommRing Rp] [CommRing Sp]
variable {ι : Type w} {f : ι → R}

/-- The comparison isomorphism in the formal gluing object obtained by base
change around a commutative square.  Equality transport occurs only at the
principal-open family index. -/
@[stacks 05EQ "formal gluing base-change comparison"]
noncomputable def baseChangeComparisonIso
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (X : FormalGluing.{u, v, w} φ f)
    (hcomm : θ.comp φ = φp.comp ψ) :
    Gluing.ofModule (fun i ↦ φp (ψ (f i)))
        ((ModuleCat.extendScalars θ).obj X.globalModule) ≅
      (X.sourceGluing.baseChange ψ).baseChange φp :=
  let e := congrArg (fun k : R →+* Sp ↦ fun i ↦ k (f i)) hcomm
  let leftComparison :
      Gluing.ofModule (fun i ↦ θ (φ (f i)))
          ((ModuleCat.extendScalars θ).obj X.globalModule) ≅
        (Gluing.changeFamilyFunctor e.symm).obj
          ((X.sourceGluing.baseChange ψ).baseChange φp) :=
    Gluing.ofModuleBaseChangeIso θ (fun i ↦ φ (f i)) X.globalModule ≪≫
      (Gluing.baseChangeFunctor θ).mapIso X.comparisonIso ≪≫
        Gluing.baseChangeCommSqIso X.sourceGluing φ ψ θ φp hcomm
  (Gluing.changeFamilyOfModuleIso e
      ((ModuleCat.extendScalars θ).obj X.globalModule)).symm ≪≫
    (Gluing.changeFamilyFunctor e).mapIso leftComparison ≪≫
      Gluing.changeFamilyInvIso e
        ((X.sourceGluing.baseChange ψ).baseChange φp)

/-- Base change of a formal gluing object around a commutative square of
ring maps. -/
@[stacks 05EQ "formal gluing base-change object"]
noncomputable def baseChangeObj
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (X : FormalGluing.{u, v, w} φ f)
    (hcomm : θ.comp φ = φp.comp ψ) :
    FormalGluing φp (fun i ↦ ψ (f i)) where
  globalModule := (ModuleCat.extendScalars θ).obj X.globalModule
  sourceGluing := X.sourceGluing.baseChange ψ
  comparisonIso := baseChangeComparisonIso φ ψ θ φp X hcomm

/-- The base-changed global and source maps form a commuting formal-gluing
comparison square. -/
@[stacks 05EQ "formal gluing base-change morphism comparison"]
theorem baseChangeMap_comm
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    {X Y : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y)
    (hcomm : θ.comp φ = φp.comp ψ) :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φp (ψ (f i)))
        ((ModuleCat.extendScalars θ).map α.globalMap))
      (baseChangeComparisonIso φ ψ θ φp X hcomm).hom
      (baseChangeComparisonIso φ ψ θ φp Y hcomm).hom
      (Gluing.baseChangeMap φp
        (Gluing.baseChangeMap ψ α.sourceMap)) := sorry

/-- Base change of a morphism of formal gluing objects. -/
@[stacks 05EQ "formal gluing base-change morphism"]
noncomputable def baseChangeMap
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    {X Y : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y)
    (hcomm : θ.comp φ = φp.comp ψ) :
    baseChangeObj φ ψ θ φp X hcomm ⟶
      baseChangeObj φ ψ θ φp Y hcomm where
  globalMap := (ModuleCat.extendScalars θ).map α.globalMap
  sourceMap := Gluing.baseChangeMap ψ α.sourceMap
  comm := baseChangeMap_comm φ ψ θ φp α hcomm

/-- Formal-gluing base change preserves identity morphisms. -/
@[stacks 05EQ "formal gluing base-change identity"]
theorem baseChangeMap_id
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (X : FormalGluing.{u, v, w} φ f)
    (hcomm : θ.comp φ = φp.comp ψ) :
    baseChangeMap φ ψ θ φp (𝟙 X) hcomm =
      𝟙 (baseChangeObj φ ψ θ φp X hcomm) := sorry

/-- Formal-gluing base change preserves composition. -/
@[stacks 05EQ "formal gluing base-change composition"]
theorem baseChangeMap_comp
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    {X Y Z : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y) (β : Y ⟶ Z)
    (hcomm : θ.comp φ = φp.comp ψ) :
    baseChangeMap φ ψ θ φp (α ≫ β) hcomm =
      baseChangeMap φ ψ θ φp α hcomm ≫
        baseChangeMap φ ψ θ φp β hcomm := sorry

/-- The base-change functor between formal gluing categories attached to a
commutative square of rings. -/
@[stacks 05EQ "formal gluing base-change functor"]
noncomputable def baseChangeFunctor
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) :
    FormalGluing.{u, v, w} φ f ⥤
      FormalGluing φp (fun i ↦ ψ (f i)) where
  obj X := baseChangeObj φ ψ θ φp X hcomm
  map α := baseChangeMap φ ψ θ φp α hcomm
  map_id := fun X ↦ baseChangeMap_id φ ψ θ φp X hcomm
  map_comp := fun α β ↦ baseChangeMap_comp φ ψ θ φp α β hcomm

/-- The global-module component of the comparison between base-changing a
canonical formal gluing object before or after applying `Can`. -/
@[stacks 05EQ "canonical formal gluing global base-change comparison"]
noncomputable def canBaseChangeGlobalIso
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    (ModuleCat.extendScalars φp).obj
        ((ModuleCat.extendScalars ψ).obj M) ≅
      (ModuleCat.extendScalars θ).obj
        ((ModuleCat.extendScalars φ).obj M) :=
  ((ModuleCat.extendScalarsCommSq θ φp φ ψ hcomm).iso.symm).app M

/-- The source-gluing component of the comparison between base-changing a
canonical formal gluing object before or after applying `Can`. -/
@[stacks 05EQ "canonical formal gluing source base-change comparison"]
noncomputable def canBaseChangeSourceIso
    (ψ : R →+* Rp) (M : ModuleCat.{max u v} R) :
    Gluing.ofModule (fun i ↦ ψ (f i))
        ((ModuleCat.extendScalars ψ).obj M) ≅
      (Gluing.ofModule f M).baseChange ψ :=
  Gluing.ofModuleBaseChangeIso ψ f M

/-- The forward global and source comparisons for `Can` form a morphism of
formal gluing objects. -/
@[stacks 05EQ "canonical formal gluing base-change forward compatibility"]
theorem canBaseChangeHom_comm
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φp (ψ (f i)))
        (canBaseChangeGlobalIso φ ψ θ φp hcomm M).hom)
      (Gluing.ofModuleBaseChangeIso φp (fun i ↦ ψ (f i))
        ((ModuleCat.extendScalars ψ).obj M)).hom
      (baseChangeComparisonIso φ ψ θ φp
        (ofModule φ f M) hcomm).hom
      (Gluing.baseChangeMap φp
        (canBaseChangeSourceIso (f := f) ψ M).hom) := sorry

/-- The forward morphism comparing `Can` after source base change with base
change of `Can`. -/
@[stacks 05EQ "canonical formal gluing base-change forward morphism"]
noncomputable def canBaseChangeHom
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    ofModule φp (fun i ↦ ψ (f i))
        ((ModuleCat.extendScalars ψ).obj M) ⟶
      baseChangeObj φ ψ θ φp (ofModule φ f M) hcomm where
  globalMap := (canBaseChangeGlobalIso φ ψ θ φp hcomm M).hom
  sourceMap := (canBaseChangeSourceIso (f := f) ψ M).hom
  comm := canBaseChangeHom_comm φ ψ θ φp hcomm M

/-- The inverse global and source comparisons for `Can` form a morphism of
formal gluing objects. -/
@[stacks 05EQ "canonical formal gluing base-change inverse compatibility"]
theorem canBaseChangeInv_comm
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φp (ψ (f i)))
        (canBaseChangeGlobalIso φ ψ θ φp hcomm M).inv)
      (baseChangeComparisonIso φ ψ θ φp
        (ofModule φ f M) hcomm).hom
      (Gluing.ofModuleBaseChangeIso φp (fun i ↦ ψ (f i))
        ((ModuleCat.extendScalars ψ).obj M)).hom
      (Gluing.baseChangeMap φp
        (canBaseChangeSourceIso (f := f) ψ M).inv) := sorry

/-- The inverse morphism comparing base change of `Can` with `Can` after
source base change. -/
@[stacks 05EQ "canonical formal gluing base-change inverse morphism"]
noncomputable def canBaseChangeInv
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    baseChangeObj φ ψ θ φp (ofModule φ f M) hcomm ⟶
      ofModule φp (fun i ↦ ψ (f i))
        ((ModuleCat.extendScalars ψ).obj M) where
  globalMap := (canBaseChangeGlobalIso φ ψ θ φp hcomm M).inv
  sourceMap := (canBaseChangeSourceIso (f := f) ψ M).inv
  comm := canBaseChangeInv_comm φ ψ θ φp hcomm M

/-- The forward and inverse `Can` base-change morphisms compose to the
identity before formal-gluing base change. -/
@[stacks 05EQ "canonical formal gluing base-change hom-inv"]
theorem canBaseChange_hom_inv_id
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    canBaseChangeHom (f := f) φ ψ θ φp hcomm M ≫
        canBaseChangeInv (f := f) φ ψ θ φp hcomm M =
      𝟙 (ofModule φp (fun i ↦ ψ (f i))
        ((ModuleCat.extendScalars ψ).obj M)) := sorry

/-- The inverse and forward `Can` base-change morphisms compose to the
identity after formal-gluing base change. -/
@[stacks 05EQ "canonical formal gluing base-change inv-hom"]
theorem canBaseChange_inv_hom_id
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    canBaseChangeInv (f := f) φ ψ θ φp hcomm M ≫
        canBaseChangeHom (f := f) φ ψ θ φp hcomm M =
      𝟙 (baseChangeObj φ ψ θ φp
        (ofModule φ f M) hcomm) := sorry

/-- The objectwise canonical isomorphism expressing that `Can` commutes
with base change. -/
@[stacks 05EQ "canonical formal gluing base-change isomorphism"]
noncomputable def canBaseChangeIso
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) (M : ModuleCat.{max u v} R) :
    ofModule φp (fun i ↦ ψ (f i))
        ((ModuleCat.extendScalars ψ).obj M) ≅
      baseChangeObj φ ψ θ φp (ofModule φ f M) hcomm where
  hom := canBaseChangeHom (f := f) φ ψ θ φp hcomm M
  inv := canBaseChangeInv (f := f) φ ψ θ φp hcomm M
  hom_inv_id := canBaseChange_hom_inv_id (f := f) φ ψ θ φp hcomm M
  inv_hom_id := canBaseChange_inv_hom_id (f := f) φ ψ θ φp hcomm M

/-- The canonical formal-gluing base-change isomorphisms are natural in the
source module. -/
@[stacks 05EQ "canonical formal gluing base-change naturality"]
theorem canBaseChange_naturality
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ)
    {M N : ModuleCat.{max u v} R} (α : M ⟶ N) :
    ((ModuleCat.extendScalars ψ ⋙
      ofModuleFunctor φp (fun i ↦ ψ (f i))).map α) ≫
        (canBaseChangeIso (f := f) φ ψ θ φp hcomm N).hom =
      (canBaseChangeIso (f := f) φ ψ θ φp hcomm M).hom ≫
        ((ofModuleFunctor φ f ⋙
          baseChangeFunctor φ ψ θ φp hcomm).map α) := sorry

/-- The natural isomorphism expressing that the canonical formal-gluing
functor commutes with base change around a commutative square of rings. -/
@[stacks 05EQ "canonical formal gluing commutative-square base change"]
noncomputable def canBaseChangeNatIso
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) :
    ModuleCat.extendScalars ψ ⋙
        ofModuleFunctor φp (fun i ↦ ψ (f i)) ≅
      ofModuleFunctor φ f ⋙
        baseChangeFunctor φ ψ θ φp hcomm :=
  NatIso.ofComponents
    (fun M ↦ canBaseChangeIso (f := f) φ ψ θ φp hcomm M)
    (fun α ↦ canBaseChange_naturality (f := f) φ ψ θ φp hcomm α)

end LocalizedModule.Away.FormalGluing
