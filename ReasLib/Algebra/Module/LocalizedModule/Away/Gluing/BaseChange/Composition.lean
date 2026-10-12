/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BaseChange
public import ReasLib.RingTheory.Localization.Away.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of base change for principal-open gluing

Base change of principal-open module gluing data is compatible with
composition of ring maps.  The local comparison is built from the canonical
localization/base-change isomorphisms and `ModuleCat.extendScalarsComp`;
only overlap compatibility and categorical coherence remain as proof units.

@stack 05EQ
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

noncomputable section

namespace LocalizedModule.Away.Gluing

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable {ι : Type w} {f : ι → R}

/-- The local comparison between iterated base change and base change along
the composite ring map. -/
@[stacks 05EQ "principal-open gluing iterated base-change local comparison"]
noncomputable def baseChangeCompLocalIso (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) (i : ι) :
    ((X.baseChange φ).baseChange ψ).localModule i ≅
      (X.baseChange (ψ.comp φ)).localModule i :=
  (X.baseChange φ).toPreGluing.baseChangeLocalModuleIso ψ i ≪≫
    (ModuleCat.extendScalars (Localization.awayMap ψ (φ (f i)))).mapIso
      (X.toPreGluing.baseChangeLocalModuleIso φ i) ≪≫
    (ModuleCat.extendScalarsComp
      (Localization.awayMap φ (f i))
      (Localization.awayMap ψ (φ (f i)))).symm.app (X.localModule i) ≪≫
    (eqToIso (congrArg ModuleCat.extendScalars
      (Localization.Away.map_comp φ ψ (f i)))).app (X.localModule i) ≪≫
    (X.toPreGluing.baseChangeLocalModuleIso (ψ.comp φ) i).symm

/-- The forward local comparisons commute with the transported overlap
isomorphisms. -/
@[stacks 05EQ "principal-open gluing iterated base-change overlap comparison"]
theorem baseChangeCompHom_comm (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers ((ψ.comp φ) (f i) * (ψ.comp φ) (f j)))
          ((baseChangeCompLocalIso X φ ψ i).hom.hom.restrictScalars T))
        (((X.baseChange φ).baseChange ψ).overlapIso i j).hom
        ((X.baseChange (ψ.comp φ)).overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers ((ψ.comp φ) (f i) * (ψ.comp φ) (f j)))
          ((baseChangeCompLocalIso X φ ψ j).hom.hom.restrictScalars T)) := sorry

/-- The forward morphism from iterated gluing base change to base change
along the composite ring map. -/
@[stacks 05EQ "principal-open gluing iterated base-change morphism"]
noncomputable def baseChangeCompHom (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) :
    (X.baseChange φ).baseChange ψ ⟶ X.baseChange (ψ.comp φ) where
  hom i := (baseChangeCompLocalIso X φ ψ i).hom
  comm := baseChangeCompHom_comm X φ ψ

/-- The inverse local comparisons commute with the transported overlap
isomorphisms. -/
@[stacks 05EQ "inverse principal-open gluing iterated base-change overlap comparison"]
theorem baseChangeCompInv_comm (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers ((ψ.comp φ) (f i) * (ψ.comp φ) (f j)))
          ((baseChangeCompLocalIso X φ ψ i).inv.hom.restrictScalars T))
        ((X.baseChange (ψ.comp φ)).overlapIso i j).hom
        (((X.baseChange φ).baseChange ψ).overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers ((ψ.comp φ) (f i) * (ψ.comp φ) (f j)))
          ((baseChangeCompLocalIso X φ ψ j).inv.hom.restrictScalars T)) := sorry

/-- The inverse morphism from composite base change to iterated gluing base
change. -/
@[stacks 05EQ "inverse principal-open gluing iterated base-change morphism"]
noncomputable def baseChangeCompInv (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) :
    X.baseChange (ψ.comp φ) ⟶ (X.baseChange φ).baseChange ψ where
  hom i := (baseChangeCompLocalIso X φ ψ i).inv
  comm := baseChangeCompInv_comm X φ ψ

/-- The forward and inverse iterated base-change morphisms compose to the
identity on the iterated base change. -/
@[stacks 05EQ "principal-open gluing iterated base-change hom-inv"]
theorem baseChangeComp_hom_inv_id (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) :
    baseChangeCompHom X φ ψ ≫ baseChangeCompInv X φ ψ =
      𝟙 ((X.baseChange φ).baseChange ψ) := sorry

/-- The inverse and forward iterated base-change morphisms compose to the
identity on base change along the composite map. -/
@[stacks 05EQ "principal-open gluing iterated base-change inv-hom"]
theorem baseChangeComp_inv_hom_id (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) :
    baseChangeCompInv X φ ψ ≫ baseChangeCompHom X φ ψ =
      𝟙 (X.baseChange (ψ.comp φ)) := sorry

/-- Iterated base change of principal-open gluing data is canonically
isomorphic to base change along the composite ring map. -/
@[stacks 05EQ "principal-open gluing base-change composition isomorphism"]
noncomputable def baseChangeCompIso (X : Gluing f)
    (φ : R →+* S) (ψ : S →+* T) :
    (X.baseChange φ).baseChange ψ ≅ X.baseChange (ψ.comp φ) where
  hom := baseChangeCompHom X φ ψ
  inv := baseChangeCompInv X φ ψ
  hom_inv_id := baseChangeComp_hom_inv_id X φ ψ
  inv_hom_id := baseChangeComp_inv_hom_id X φ ψ

/-- The iterated base-change comparison is natural in the gluing datum. -/
@[stacks 05EQ "principal-open gluing base-change composition naturality"]
theorem baseChangeComp_naturality (φ : R →+* S) (ψ : S →+* T)
    {X Y : Gluing f} (α : X ⟶ Y) :
    ((baseChangeFunctor φ ⋙ baseChangeFunctor ψ).map α) ≫
        (baseChangeCompIso Y φ ψ).hom =
      (baseChangeCompIso X φ ψ).hom ≫
        (baseChangeFunctor (ψ.comp φ)).map α := sorry

/-- The canonical natural isomorphism from iterated gluing base change to
base change along the composite ring map. -/
@[stacks 05EQ "principal-open gluing base-change composition natural isomorphism"]
noncomputable def baseChangeCompNatIso (φ : R →+* S) (ψ : S →+* T) :
    baseChangeFunctor (f := f) φ ⋙ baseChangeFunctor ψ ≅
      baseChangeFunctor (ψ.comp φ) :=
  NatIso.ofComponents (fun X ↦ baseChangeCompIso X φ ψ)
    (fun α ↦ baseChangeComp_naturality φ ψ α)

end LocalizedModule.Away.Gluing
