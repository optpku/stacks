module

public import ReasLib.RingTheory.DividedPowers.PrincipalCompletion
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem.Limits
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DividedPowerDifferential

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
variable (h_nilpotent : IsNilpotent (p : B ⧸ J))

/-- The positive index shifted by the stable principal-power offset. -/
noncomputable def offsetIndex (e : ℕ+) : ℕ+ :=
  ⟨(e : ℕ) + DividedPowers.PrincipalCompletion.stableOffset p h_nilpotent,
    Nat.add_pos_left e.pos _⟩

/-- The stable quotient ring with its induced divided powers. -/
noncomputable abbrev stableStageRing (e : ℕ+) : DividedPowerRing :=
  DividedPowers.QuotientPowerTower.stage δ (Ideal.span {(p : B)})
    (DividedPowers.PrincipalCompletion.stableOffset p h_nilpotent)
    (DividedPowers.PrincipalCompletion.stableOffset_isStable δ p h_nilpotent) (e : ℕ)

/-- The Kähler module for the specified ring homomorphism. -/
noncomputable abbrev originalKaehlerModule : ModuleCat.{u} B :=
  -- Local instance justification (noncanonical choice): the Kähler module depends on the explicit base map f rather than an ambient algebra.
  letI : Algebra A B := f.toAlgebra
  ModuleCat.of B (KaehlerDifferential A B)

/-- The Kähler module of a stable quotient, restricted along its quotient map. -/
noncomputable abbrev stableKaehlerStage (e : ℕ+) : ModuleCat.{u} B :=
  let S := stableStageRing δ p h_nilpotent e
  let q : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
  -- Local instance justification (noncanonical choice): the relative Kähler module uses the composite of f and this quotient map.
  letI : Algebra A S := (q.comp f).toAlgebra
  (ModuleCat.restrictScalars q).obj (ModuleCat.of S (KaehlerDifferential A S))

/-- The relative divided-power differential of a stable quotient, restricted to the original ring. -/
noncomputable abbrev stableStage (e : ℕ+) : ModuleCat.{u} B :=
  let S := stableStageRing δ p h_nilpotent e
  let q : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
  -- Local instance justification (noncanonical choice): the relative divided-power differential uses the composite base map q.comp f.
  letI : Algebra A S := (q.comp f).toAlgebra
  (ModuleCat.restrictScalars q).obj
    (ModuleCat.of S (KaehlerDifferential.DeRham.dividedPowerDifferential (q.comp f) S.dividedPowers))

/-- The quotient-factor transition between stable quotient rings. -/
noncomputable def stableStageRingHom {i j : ℕ+} (hij : j ≤ i) :
    stableStageRing δ p h_nilpotent i →+* stableStageRing δ p h_nilpotent j :=
  Ideal.Quotient.factor <| Ideal.pow_le_pow_right <|
    Nat.add_le_add_right hij (DividedPowers.PrincipalCompletion.stableOffset p h_nilpotent)

/-- The Kähler map of a stable quotient transition with its restricted scalar actions. -/
noncomputable def stableStageKaehlerMap {i j : ℕ+} (hij : j ≤ i) :
    stableKaehlerStage f δ p h_nilpotent i →ₗ[B] stableKaehlerStage f δ p h_nilpotent j :=
  let restrictionMap
      (base source target : Type u) [CommRing base] [CommRing source] [CommRing target]
      [Algebra base source] [Algebra base target] [Algebra source target]
      [IsScalarTower base source target] :
      ModuleCat.of source (KaehlerDifferential base source) ⟶
        (ModuleCat.restrictScalars (algebraMap source target)).obj
          (ModuleCat.of target (KaehlerDifferential base target)) :=
    let native := KaehlerDifferential.map base base source target
    ModuleCat.ofHom (X := ModuleCat.of source (KaehlerDifferential base source))
      (Y := (ModuleCat.restrictScalars (algebraMap source target)).obj
        (ModuleCat.of target (KaehlerDifferential base target)))
      { toFun := native
        map_add' := native.map_add
        map_smul' := fun scalar differential ↦ (native.map_smul scalar differential).trans
          (IsScalarTower.algebraMap_smul target scalar (native differential)).symm }
  let Si := stableStageRing δ p h_nilpotent i
  let Sj := stableStageRing δ p h_nilpotent j
  let qi : B →+* Si := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent i : ℕ))
  let qj : B →+* Sj := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent j : ℕ))
  let φ := stableStageRingHom δ p h_nilpotent hij
  let inclusion : Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent i : ℕ) ≤
      Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent j : ℕ) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right hij
      (DividedPowers.PrincipalCompletion.stableOffset p h_nilpotent))
  -- Local instance justification (noncanonical choice): both Kähler modules depend on the specified quotient composites of f.
  letI : Algebra A Si := (qi.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): the target base action is the specified quotient composite of f.
  letI : Algebra A Sj := (qj.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): the transition algebra is induced by the explicit quotient-factor map.
  letI : Algebra Si Sj := φ.toAlgebra
  -- Local instance justification (defeq pin): quotient-factor compatibility supplies the canonical tower for the Kähler map.
  letI : IsScalarTower A Si Sj := IsScalarTower.of_algebraMap_eq
    (fun scalar ↦ (Ideal.Quotient.factor_mk inclusion (f scalar)).symm)
  let target := ModuleCat.of Sj (KaehlerDifferential A Sj)
  ((ModuleCat.restrictScalars qi).map (restrictionMap A Si Sj) ≫
    (ModuleCat.restrictScalarsComp'App qi φ qj (Ideal.Quotient.factor_comp_mk inclusion).symm target).inv).hom

/-- Stable quotient transitions carry divided-power relations into divided-power relations. -/
theorem stableStageKaehlerMap_relations {i j : ℕ+} (hij : j ≤ i) :
    let Si := stableStageRing δ p h_nilpotent i
    let Sj := stableStageRing δ p h_nilpotent j
    let qi : B →+* Si := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent i : ℕ))
    let qj : B →+* Sj := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent j : ℕ))
    -- Local instance justification (noncanonical choice): the relation submodule uses the explicit composite base map.
    letI : Algebra A Si := (qi.comp f).toAlgebra
    -- Local instance justification (noncanonical choice): the target relation submodule uses the explicit composite base map.
    letI : Algebra A Sj := (qj.comp f).toAlgebra
    -- Local instance justification (noncanonical choice): relation restriction follows the specified source quotient homomorphism.
    letI : Algebra B Si := qi.toAlgebra
    -- Local instance justification (noncanonical choice): relation restriction follows the specified target quotient homomorphism.
    letI : Algebra B Sj := qj.toAlgebra
    -- Local instance justification (defeq pin): relation restriction uses the source B-action stored in stableKaehlerStage.
    letI : Module B (KaehlerDifferential A Si) := (stableKaehlerStage f δ p h_nilpotent i).isModule
    -- Local instance justification (defeq pin): relation restriction uses the target B-action stored in stableKaehlerStage.
    letI : Module B (KaehlerDifferential A Sj) := (stableKaehlerStage f δ p h_nilpotent j).isModule
    -- Local instance justification (defeq pin): source relation restriction needs the scalar tower of its stored compHom action.
    letI : IsScalarTower B Si (KaehlerDifferential A Si) := IsScalarTower.of_compHom B Si (KaehlerDifferential A Si)
    -- Local instance justification (defeq pin): target relation restriction needs the scalar tower of its stored compHom action.
    letI : IsScalarTower B Sj (KaehlerDifferential A Sj) := IsScalarTower.of_compHom B Sj (KaehlerDifferential A Sj)
    (KaehlerDifferential.DeRham.dividedPowerRelations (qi.comp f) Si.dividedPowers).restrictScalars B ≤
      ((KaehlerDifferential.DeRham.dividedPowerRelations (qj.comp f) Sj.dividedPowers).restrictScalars B).comap
        (stableStageKaehlerMap f δ p h_nilpotent hij) := sorry

/-- The induced transition on divided-power differential quotient modules. -/
noncomputable def stableStageMap {i j : ℕ+} (hij : j ≤ i) :
    stableStage f δ p h_nilpotent i ⟶ stableStage f δ p h_nilpotent j :=
  let Si := stableStageRing δ p h_nilpotent i
  let Sj := stableStageRing δ p h_nilpotent j
  let qi : B →+* Si := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent i : ℕ))
  let qj : B →+* Sj := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent j : ℕ))
  -- Local instance justification (noncanonical choice): quotient descent uses the explicitly specified base map at the source.
  letI : Algebra A Si := (qi.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): quotient descent uses the explicitly specified base map at the target.
  letI : Algebra A Sj := (qj.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): scalar restriction uses the specified source quotient map.
  letI : Algebra B Si := qi.toAlgebra
  -- Local instance justification (noncanonical choice): scalar restriction uses the specified target quotient map.
  letI : Algebra B Sj := qj.toAlgebra
  -- Local instance justification (defeq pin): quotient descent uses the source action of the bundled restricted Kähler module.
  letI : Module B (KaehlerDifferential A Si) := (stableKaehlerStage f δ p h_nilpotent i).isModule
  -- Local instance justification (defeq pin): quotient descent uses the target action of the bundled restricted Kähler module.
  letI : Module B (KaehlerDifferential A Sj) := (stableKaehlerStage f δ p h_nilpotent j).isModule
  -- Local instance justification (defeq pin): the source quotient-restriction equivalence needs the canonical compHom tower.
  letI : IsScalarTower B Si (KaehlerDifferential A Si) := IsScalarTower.of_compHom B _ _
  -- Local instance justification (defeq pin): the target quotient-restriction equivalence needs the canonical compHom tower.
  letI : IsScalarTower B Sj (KaehlerDifferential A Sj) := IsScalarTower.of_compHom B _ _
  let sourceRelations := KaehlerDifferential.DeRham.dividedPowerRelations (qi.comp f) Si.dividedPowers
  let targetRelations := KaehlerDifferential.DeRham.dividedPowerRelations (qj.comp f) Sj.dividedPowers
  ModuleCat.ofHom <| (Submodule.Quotient.restrictScalarsEquiv B targetRelations).toLinearMap ∘ₗ
    (sourceRelations.restrictScalars B).mapQ (targetRelations.restrictScalars B)
      (stableStageKaehlerMap f δ p h_nilpotent hij)
      (stableStageKaehlerMap_relations f δ p h_nilpotent hij) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv B sourceRelations).symm.toLinearMap

/-- A stable differential transition at an unchanged index is the identity. -/
theorem stableStageMap_id (e : ℕ+) :
    stableStageMap f δ p h_nilpotent (le_refl e) = 𝟙 (stableStage f δ p h_nilpotent e) := sorry

/-- Stable differential transitions compose along inequalities of indices. -/
theorem stableStageMap_comp {i j k : ℕ+} (hij : j ≤ i) (hjk : k ≤ j) :
    stableStageMap f δ p h_nilpotent (hjk.trans hij) =
      stableStageMap f δ p h_nilpotent hij ≫ stableStageMap f δ p h_nilpotent hjk := sorry

/-- The inverse system of stable quotient divided-power differential modules. -/
noncomputable def stableSystem : PNatInverseSystem (ModuleCat.{u} B) where
  obj index := stableStage f δ p h_nilpotent (OrderDual.ofDual index)
  map transition := stableStageMap f δ p h_nilpotent (leOfHom transition)
  map_id index := stableStageMap_id f δ p h_nilpotent (OrderDual.ofDual index)
  map_comp first second := stableStageMap_comp f δ p h_nilpotent (leOfHom first) (leOfHom second)

/-- The stage of the stable inverse system is its specified differential module. -/
theorem stableSystem_stage (e : ℕ+) :
    (stableSystem f δ p h_nilpotent).stage e = stableStage f δ p h_nilpotent e := rfl

/-- The principal-adic completion with divided powers on the kernel of its quotient map. -/
noncomputable abbrev completedRing : DividedPowerRing :=
  let offset := DividedPowers.PrincipalCompletion.stableOffset p h_nilpotent
  let hpow := DividedPowers.PrincipalCompletion.stableOffset_pow_le δ p h_nilpotent
  DividedPowers.QuotientPowerTower.completion (Ideal.span {(p : B)}) offset hpow
    (DividedPowers.PrincipalCompletion.powers δ p offset hpow)

/-- The completed relative Kähler module, restricted to the original ring. -/
noncomputable abbrev completedKaehlerModule : ModuleCat.{u} B :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  let q : B →+* R := algebraMap B R
  -- Local instance justification (noncanonical choice): the completion's base algebra is the composite of f with the completion homomorphism.
  letI : Algebra A R := (q.comp f).toAlgebra
  (ModuleCat.restrictScalars q).obj (ModuleCat.of R (KaehlerDifferential A R))

/-- The relative divided-power differential module of the completed ring. -/
noncomputable abbrev completedDifferential : Type u :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  KaehlerDifferential.DeRham.dividedPowerDifferential ((algebraMap B R).comp f)
    (completedRing δ p h_nilpotent).dividedPowers

/-- The completed divided-power differential module with its restricted original-ring action. -/
noncomputable abbrev completedModule : ModuleCat.{u} B :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  -- Local instance justification (noncanonical choice): the completed differential is relative to the prescribed composite of f.
  letI : Algebra A R := ((algebraMap B R).comp f).toAlgebra
  (ModuleCat.restrictScalars (algebraMap B R)).obj
    (ModuleCat.of R (completedDifferential f δ p h_nilpotent))

/-- The positive principal-power quotient system of the completed differential, restricted to the original ring. -/
noncomputable def completedSystem : PNatInverseSystem (ModuleCat.{u} B) :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  -- Local instance justification (noncanonical choice): the coefficient-ring quotient system uses the completed differential for the explicit base map f.
  letI : Algebra A R := ((algebraMap B R).comp f).toAlgebra
  AdicCompletion.positiveQuotientSystem (Ideal.span {(p : R)})
    (completedDifferential f δ p h_nilpotent) ⋙ ModuleCat.restrictScalars (algebraMap B R)

/-- The positive principal-power quotient system of the original divided-power differential. -/
noncomputable abbrev originalSystem : PNatInverseSystem (ModuleCat.{u} B) :=
  -- Local instance justification (noncanonical choice): the original differential depends on the explicitly specified base map f.
  letI : Algebra A B := f.toAlgebra
  AdicCompletion.positiveQuotientSystem (Ideal.span {(p : B)})
    (KaehlerDifferential.DeRham.dividedPowerDifferential f δ)

/-- The Kähler map induced by the quotient to a stable stage. -/
noncomputable def originalStageKaehlerMap (e : ℕ+) :
    originalKaehlerModule f →ₗ[B] stableKaehlerStage f δ p h_nilpotent e :=
  let S := stableStageRing δ p h_nilpotent e
  let q : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
  -- Local instance justification (noncanonical choice): the original Kähler module is relative to the explicit base map f.
  letI : Algebra A B := f.toAlgebra
  -- Local instance justification (noncanonical choice): the target Kähler module is relative to the composite quotient base map.
  letI : Algebra A S := (q.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): the quotient induces the scalar action used by the differential map.
  letI : Algebra B S := q.toAlgebra
  -- Local instance justification (defeq pin): the composite quotient algebra has the canonical scalar tower needed by KaehlerDifferential.map.
  letI : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  -- Local instance justification (defeq pin): the codomain action is the one stored in stableKaehlerStage.
  letI : Module B (KaehlerDifferential A S) := (stableKaehlerStage f δ p h_nilpotent e).isModule
  -- Local instance justification (defeq pin): the bundled restricted action is compatible with the quotient-ring action.
  letI : IsScalarTower B S (KaehlerDifferential A S) := IsScalarTower.of_compHom B _ _
  KaehlerDifferential.map A A B S

/-- The quotient Kähler map preserves the divided-power relation submodules. -/
theorem originalStageKaehlerMap_relations (e : ℕ+) :
    let S := stableStageRing δ p h_nilpotent e
    let q : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
    -- Local instance justification (noncanonical choice): original relations are formed relative to the explicit base map f.
    letI : Algebra A B := f.toAlgebra
    -- Local instance justification (noncanonical choice): quotient relations are formed relative to the composite base map.
    letI : Algebra A S := (q.comp f).toAlgebra
    -- Local instance justification (noncanonical choice): relation restriction follows the specified quotient homomorphism.
    letI : Algebra B S := q.toAlgebra
    -- Local instance justification (defeq pin): the restricted relation submodule carries the action stored in stableKaehlerStage.
    letI : Module B (KaehlerDifferential A S) := (stableKaehlerStage f δ p h_nilpotent e).isModule
    -- Local instance justification (defeq pin): relation restriction needs the scalar tower of its stored compHom action.
    letI : IsScalarTower B S (KaehlerDifferential A S) := IsScalarTower.of_compHom B S (KaehlerDifferential A S)
    KaehlerDifferential.DeRham.dividedPowerRelations f δ ≤
      ((KaehlerDifferential.DeRham.dividedPowerRelations (q.comp f) S.dividedPowers).restrictScalars B).comap
        (originalStageKaehlerMap f δ p h_nilpotent e) := sorry

/-- The original divided-power differential map to a stable quotient differential. -/
noncomputable def originalStageLinearMap (e : ℕ+) :
    -- Local instance justification (noncanonical choice): the source differential uses the explicitly prescribed base map f.
    letI : Algebra A B := f.toAlgebra
    (ModuleCat.of B (KaehlerDifferential.DeRham.dividedPowerDifferential f δ)) →ₗ[B]
      stableStage f δ p h_nilpotent e :=
  let S := stableStageRing δ p h_nilpotent e
  let q : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
  -- Local instance justification (noncanonical choice): quotient descent is relative to the specified base map f.
  letI : Algebra A B := f.toAlgebra
  -- Local instance justification (noncanonical choice): quotient descent at the target uses the composite base map.
  letI : Algebra A S := (q.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): restriction of the quotient relations uses the specified quotient map.
  letI : Algebra B S := q.toAlgebra
  -- Local instance justification (defeq pin): descent uses the target action stored in stableKaehlerStage.
  letI : Module B (KaehlerDifferential A S) := (stableKaehlerStage f δ p h_nilpotent e).isModule
  -- Local instance justification (defeq pin): the quotient-restriction equivalence uses the canonical compHom tower.
  letI : IsScalarTower B S (KaehlerDifferential A S) := IsScalarTower.of_compHom B _ _
  let targetRelations := KaehlerDifferential.DeRham.dividedPowerRelations (q.comp f) S.dividedPowers
  (Submodule.Quotient.restrictScalarsEquiv B targetRelations).toLinearMap ∘ₗ
    (KaehlerDifferential.DeRham.dividedPowerRelations f δ).mapQ (targetRelations.restrictScalars B)
      (originalStageKaehlerMap f δ p h_nilpotent e)
      (originalStageKaehlerMap_relations f δ p h_nilpotent e)

/-- The shifted principal-power submodule lies in the kernel of the original differential comparison. -/
theorem originalStageLinearMap_pow_smul (e : ℕ+) :
    -- Local instance justification (noncanonical choice): the principal-power submodule uses the differential for the explicit base map f.
    letI : Algebra A B := f.toAlgebra
    Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ) •
        (⊤ : Submodule B (KaehlerDifferential.DeRham.dividedPowerDifferential f δ)) ≤
      LinearMap.ker (originalStageLinearMap f δ p h_nilpotent e) := sorry

/-- The comparison from the shifted original differential quotient to a stable stage. -/
noncomputable def originalStageComparison (e : ℕ+) :
    (originalSystem f δ p).stage (offsetIndex p h_nilpotent e) ⟶
      (stableSystem f δ p h_nilpotent).stage e :=
  -- Local instance justification (noncanonical choice): quotient descent uses the differential for the specified base map f.
  letI : Algebra A B := f.toAlgebra
  ModuleCat.ofHom (X := (originalSystem f δ p).stage (offsetIndex p h_nilpotent e))
    (Y := (stableSystem f δ p h_nilpotent).stage e) <|
    (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ) •
      (⊤ : Submodule B (KaehlerDifferential.DeRham.dividedPowerDifferential f δ))).liftQ
      (originalStageLinearMap f δ p h_nilpotent e)
      (originalStageLinearMap_pow_smul f δ p h_nilpotent e)

/-- The Kähler map of evaluation from the completion to a stable quotient. -/
noncomputable def completionStageKaehlerMap (e : ℕ+) :
    completedKaehlerModule f p →ₗ[B] stableKaehlerStage f δ p h_nilpotent e :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  let S := stableStageRing δ p h_nilpotent e
  let qB : B →+* R := algebraMap B R
  let qS : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
  let ev : R →+* S := (AdicCompletion.evalₐ (Ideal.span {(p : B)}) (offsetIndex p h_nilpotent e : ℕ)).toRingHom
  -- Local instance justification (noncanonical choice): the completed Kähler module uses the prescribed composite base map.
  letI : Algebra A R := (qB.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): the stable Kähler module uses the prescribed composite quotient base map.
  letI : Algebra A S := (qS.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): evaluation induces the R-action used by the differential map.
  letI : Algebra R S := ev.toAlgebra
  -- Local instance justification (defeq pin): evaluation commutes with the original-ring algebra map, giving its base scalar tower.
  letI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq
    (fun scalar ↦ ((AdicCompletion.evalₐ (Ideal.span {(p : B)})
      (offsetIndex p h_nilpotent e : ℕ)).commutes (f scalar)).symm)
  let target := ModuleCat.of S (KaehlerDifferential A S)
  -- Local instance justification (defeq pin): the differential map uses the R-action stored by restriction along evaluation.
  letI : Module R (KaehlerDifferential A S) := Module.compHom _ ev
  -- Local instance justification (defeq pin): the restricted evaluation action has the canonical compHom scalar tower.
  letI : IsScalarTower R S (KaehlerDifferential A S) := IsScalarTower.of_compHom R S (KaehlerDifferential A S)
  let native : ModuleCat.of R (KaehlerDifferential A R) ⟶ (ModuleCat.restrictScalars ev).obj target :=
    ModuleCat.ofHom (KaehlerDifferential.map A A R S)
  ((ModuleCat.restrictScalars qB).map native ≫
    (ModuleCat.restrictScalarsComp'App qB ev qS
      (RingHom.ext (fun scalar ↦ ((AdicCompletion.evalₐ (Ideal.span {(p : B)})
        (offsetIndex p h_nilpotent e : ℕ)).commutes scalar).symm)) target).inv).hom

/-- Evaluation carries completed divided-power relations into the stable quotient relations. -/
theorem completionStageKaehlerMap_relations (e : ℕ+) :
    let R := AdicCompletion (Ideal.span {(p : B)}) B
    let S := stableStageRing δ p h_nilpotent e
    let qB : B →+* R := algebraMap B R
    let qS : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
    -- Local instance justification (noncanonical choice): completed relations are relative to the specified composite base map.
    letI : Algebra A R := (qB.comp f).toAlgebra
    -- Local instance justification (noncanonical choice): quotient relations are relative to the specified composite quotient base map.
    letI : Algebra A S := (qS.comp f).toAlgebra
    -- Local instance justification (defeq pin): completed relation restriction uses the action stored in completedKaehlerModule.
    letI : Module B (KaehlerDifferential A R) := (completedKaehlerModule f p).isModule
    -- Local instance justification (noncanonical choice): quotient relation restriction follows the specified quotient homomorphism.
    letI : Algebra B S := qS.toAlgebra
    -- Local instance justification (defeq pin): quotient relation restriction uses the action stored in stableKaehlerStage.
    letI : Module B (KaehlerDifferential A S) := (stableKaehlerStage f δ p h_nilpotent e).isModule
    -- Local instance justification (defeq pin): completed relation restriction needs the scalar tower of its stored compHom action.
    letI : IsScalarTower B R (KaehlerDifferential A R) := IsScalarTower.of_compHom B R (KaehlerDifferential A R)
    -- Local instance justification (defeq pin): quotient relation restriction needs the scalar tower of its stored compHom action.
    letI : IsScalarTower B S (KaehlerDifferential A S) := IsScalarTower.of_compHom B S (KaehlerDifferential A S)
    (KaehlerDifferential.DeRham.dividedPowerRelations (qB.comp f)
      (completedRing δ p h_nilpotent).dividedPowers).restrictScalars B ≤
      ((KaehlerDifferential.DeRham.dividedPowerRelations (qS.comp f) S.dividedPowers).restrictScalars B).comap
        (completionStageKaehlerMap f δ p h_nilpotent e) := sorry

/-- Evaluation on the completed divided-power differential, with restricted scalar actions. -/
noncomputable def completionStageLinearMap (e : ℕ+) :
    completedModule f δ p h_nilpotent →ₗ[B] stableStage f δ p h_nilpotent e :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  let S := stableStageRing δ p h_nilpotent e
  let qB : B →+* R := algebraMap B R
  let qS : B →+* S := Ideal.Quotient.mk (Ideal.span {(p : B)} ^ (offsetIndex p h_nilpotent e : ℕ))
  -- Local instance justification (noncanonical choice): completed quotient descent uses the prescribed composite base map.
  letI : Algebra A R := (qB.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): target quotient descent uses the prescribed quotient base map.
  letI : Algebra A S := (qS.comp f).toAlgebra
  -- Local instance justification (noncanonical choice): quotient restriction at the target uses its specified quotient map.
  letI : Algebra B S := qS.toAlgebra
  -- Local instance justification (defeq pin): completed descent uses the action stored in completedKaehlerModule.
  letI : Module B (KaehlerDifferential A R) := (completedKaehlerModule f p).isModule
  -- Local instance justification (defeq pin): target descent uses the action stored in stableKaehlerStage.
  letI : Module B (KaehlerDifferential A S) := (stableKaehlerStage f δ p h_nilpotent e).isModule
  -- Local instance justification (defeq pin): completed quotient restriction uses the canonical compHom tower.
  letI : IsScalarTower B R (KaehlerDifferential A R) := IsScalarTower.of_compHom B _ _
  -- Local instance justification (defeq pin): target quotient restriction uses the canonical compHom tower.
  letI : IsScalarTower B S (KaehlerDifferential A S) := IsScalarTower.of_compHom B _ _
  let sourceRelations := KaehlerDifferential.DeRham.dividedPowerRelations (qB.comp f)
    (completedRing δ p h_nilpotent).dividedPowers
  let targetRelations := KaehlerDifferential.DeRham.dividedPowerRelations (qS.comp f) S.dividedPowers
  (Submodule.Quotient.restrictScalarsEquiv B targetRelations).toLinearMap ∘ₗ
    (sourceRelations.restrictScalars B).mapQ (targetRelations.restrictScalars B)
      (completionStageKaehlerMap f δ p h_nilpotent e)
      (completionStageKaehlerMap_relations f δ p h_nilpotent e) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv B sourceRelations).symm.toLinearMap

/-- The shifted completed principal-power submodule lies in the evaluation differential kernel. -/
theorem completionStageLinearMap_pow_smul (e : ℕ+) :
    let R := AdicCompletion (Ideal.span {(p : B)}) B
    -- Local instance justification (noncanonical choice): the completed differential quotient is relative to the prescribed composite base map.
    letI : Algebra A R := ((algebraMap B R).comp f).toAlgebra
    -- Local instance justification (defeq pin): kernel containment uses the B-action stored in completedModule.
    letI : Module B (completedDifferential f δ p h_nilpotent) := (completedModule f δ p h_nilpotent).isModule
    -- Local instance justification (defeq pin): prevent the raw quotient SMul instance from replacing the bundled completion action in the scalar tower.
    letI : SMul B (completedDifferential f δ p h_nilpotent) := (completedModule f δ p h_nilpotent).isModule.toSMul
    -- Local instance justification (defeq pin): the restricted kernel submodule needs the scalar tower of the stored compHom action.
    letI : IsScalarTower B R (completedDifferential f δ p h_nilpotent) :=
      IsScalarTower.of_compHom B R (completedDifferential f δ p h_nilpotent)
    (Ideal.span {(p : R)} ^ (offsetIndex p h_nilpotent e : ℕ) •
      (⊤ : Submodule R (completedDifferential f δ p h_nilpotent))).restrictScalars B ≤
      LinearMap.ker (completionStageLinearMap f δ p h_nilpotent e) := sorry

/-- The comparison from the shifted completed differential quotient to a stable stage. -/
noncomputable def completionStageComparison (e : ℕ+) :
    (completedSystem f δ p h_nilpotent).stage (offsetIndex p h_nilpotent e) ⟶
      (stableSystem f δ p h_nilpotent).stage e :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  -- Local instance justification (noncanonical choice): the completed quotient system uses the prescribed composite base map.
  letI : Algebra A R := ((algebraMap B R).comp f).toAlgebra
  -- Local instance justification (defeq pin): quotient descent uses the completed module's stored B-action.
  letI : Module B (completedDifferential f δ p h_nilpotent) := (completedModule f δ p h_nilpotent).isModule
  -- Local instance justification (defeq pin): prevent the raw quotient SMul instance from replacing the bundled completion action in quotient restriction.
  letI : SMul B (completedDifferential f δ p h_nilpotent) := (completedModule f δ p h_nilpotent).isModule.toSMul
  -- Local instance justification (defeq pin): completed quotient restriction uses the canonical compHom tower.
  letI : IsScalarTower B R (completedDifferential f δ p h_nilpotent) := IsScalarTower.of_compHom B _ _
  let relations := Ideal.span {(p : R)} ^ (offsetIndex p h_nilpotent e : ℕ) •
    (⊤ : Submodule R (completedDifferential f δ p h_nilpotent))
  ModuleCat.ofHom (X := (completedSystem f δ p h_nilpotent).stage (offsetIndex p h_nilpotent e))
    (Y := (stableSystem f δ p h_nilpotent).stage e) <| (relations.restrictScalars B).liftQ
    (completionStageLinearMap f δ p h_nilpotent e)
    (completionStageLinearMap_pow_smul f δ p h_nilpotent e) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv B relations).symm.toLinearMap

variable [Fact (Nat.Prime p)] [Algebra (Int.LocalizationAtPrime p) A]

/-- The shifted original quotient comparisons define a natural cone over the stable differential system. -/
theorem originalStageComparison_naturality {index target : OrderDual ℕ+} (transition : index ⟶ target) :
    𝟙 (limit (originalSystem f δ p)) ≫
        ((originalSystem f δ p).limitProjection (offsetIndex p h_nilpotent (OrderDual.ofDual target)) ≫
          originalStageComparison f δ p h_nilpotent (OrderDual.ofDual target)) =
      ((originalSystem f δ p).limitProjection (offsetIndex p h_nilpotent (OrderDual.ofDual index)) ≫
        originalStageComparison f δ p h_nilpotent (OrderDual.ofDual index)) ≫
          (stableSystem f δ p h_nilpotent).map transition := sorry

/-- The cone induced by the shifted original differential quotient comparisons. -/
noncomputable def originalLimitComparisonCone : Cone (stableSystem f δ p h_nilpotent) where
  pt := limit (originalSystem f δ p)
  π :=
    { app := fun index ↦
        (originalSystem f δ p).limitProjection (offsetIndex p h_nilpotent (OrderDual.ofDual index)) ≫
          originalStageComparison f δ p h_nilpotent (OrderDual.ofDual index)
      naturality := fun _ _ transition ↦ originalStageComparison_naturality f δ p h_nilpotent transition }

/-- The canonical map from the original differential quotient limit to the stable quotient differential limit. -/
noncomputable def originalLimitComparison :
    limit (originalSystem f δ p) ⟶ limit (stableSystem f δ p h_nilpotent) :=
  limit.lift (stableSystem f δ p h_nilpotent) (originalLimitComparisonCone f δ p h_nilpotent)

/-- The original limit comparison projects to its shifted-stage quotient comparison. -/
theorem originalLimitComparison_comp_limitProjection (e : ℕ+) :
    originalLimitComparison f δ p h_nilpotent ≫ (stableSystem f δ p h_nilpotent).limitProjection e =
      (originalSystem f δ p).limitProjection (offsetIndex p h_nilpotent e) ≫
        originalStageComparison f δ p h_nilpotent e := sorry

/-- The canonical comparison from original differential quotients to stable quotient differentials is invertible. -/
instance originalLimitComparison_isIso : IsIso (originalLimitComparison f δ p h_nilpotent) := sorry

/-- The shifted completed quotient comparisons define a natural cone over the stable differential system. -/
theorem completionStageComparison_naturality {index target : OrderDual ℕ+} (transition : index ⟶ target) :
    𝟙 (limit (completedSystem f δ p h_nilpotent)) ≫
        ((completedSystem f δ p h_nilpotent).limitProjection
          (offsetIndex p h_nilpotent (OrderDual.ofDual target)) ≫
            completionStageComparison f δ p h_nilpotent (OrderDual.ofDual target)) =
      ((completedSystem f δ p h_nilpotent).limitProjection
        (offsetIndex p h_nilpotent (OrderDual.ofDual index)) ≫
          completionStageComparison f δ p h_nilpotent (OrderDual.ofDual index)) ≫
            (stableSystem f δ p h_nilpotent).map transition := sorry

/-- The cone induced by the shifted completed differential quotient comparisons. -/
noncomputable def completionLimitComparisonCone : Cone (stableSystem f δ p h_nilpotent) where
  pt := limit (completedSystem f δ p h_nilpotent)
  π :=
    { app := fun index ↦
        (completedSystem f δ p h_nilpotent).limitProjection
          (offsetIndex p h_nilpotent (OrderDual.ofDual index)) ≫
            completionStageComparison f δ p h_nilpotent (OrderDual.ofDual index)
      naturality := fun _ _ transition ↦ completionStageComparison_naturality f δ p h_nilpotent transition }

/-- The canonical map from the completed differential quotient limit to the stable quotient differential limit. -/
noncomputable def completionLimitComparison :
    limit (completedSystem f δ p h_nilpotent) ⟶ limit (stableSystem f δ p h_nilpotent) :=
  limit.lift (stableSystem f δ p h_nilpotent) (completionLimitComparisonCone f δ p h_nilpotent)

/-- The completed limit comparison projects to its shifted-stage evaluation comparison. -/
theorem completionLimitComparison_comp_limitProjection (e : ℕ+) :
    completionLimitComparison f δ p h_nilpotent ≫ (stableSystem f δ p h_nilpotent).limitProjection e =
      (completedSystem f δ p h_nilpotent).limitProjection (offsetIndex p h_nilpotent e) ≫
        completionStageComparison f δ p h_nilpotent e := sorry

/-- The canonical comparison from completed differential quotients to stable quotient differentials is invertible. -/
instance completionLimitComparison_isIso : IsIso (completionLimitComparison f δ p h_nilpotent) := sorry

end DividedPowerDifferential
