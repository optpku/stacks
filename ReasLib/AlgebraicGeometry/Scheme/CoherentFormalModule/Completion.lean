/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# Completion of coherent modules

The completion functor is built explicitly from the inverse system of ideal-power quotient
module sheaves. Its object and morphism data are therefore available independently of the
proofs that the stages are coherent and satisfy the formal-module axioms.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The module sheaf `ℱ / I ^ n ℱ` underlying stage `n` of coherent completion. -/
@[stacks 0880 "ideal-power quotient stage of coherent completion"]
noncomputable abbrev Stage (I : X.IdealSheafData)
    (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ) : X.Modules :=
  SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
    I.toSubobject ℱ.obj n

/-- Every ideal-power quotient stage of a coherent module on a Noetherian scheme is coherent. -/
@[stacks 0880 "coherence of ideal-power quotient stages"]
theorem stage_isCoherent (I : X.IdealSheafData)
    (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ) :
    (Stage I ℱ n).IsCoherent := sorry

/-- Stage `n` of coherent completion, as an object of the coherent-module category. -/
@[stacks 0880 "coherent ideal-power quotient stage"]
def stage (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ) :
    RingedSpace.Coh X.toRingedSpace :=
  ⟨Stage I ℱ n, stage_isCoherent I ℱ n⟩

/-- The transition `ℱ / I ^ (n + 1) ℱ ⟶ ℱ / I ^ n ℱ` in coherent modules. -/
@[stacks 0880 "transition of coherent completion"]
def step (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ) :
    stage I ℱ (n + 1) ⟶ stage I ℱ n :=
  ObjectProperty.homMk
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.step.{u, u, u}
      I.toSubobject ℱ.obj n)

/-- The explicit inverse system `n ↦ ℱ / I ^ n ℱ` of coherent modules. -/
@[stacks 0880 "inverse system defining coherent completion"]
def system (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace) :
    SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace) :=
  Functor.ofOpSequence (step I ℱ)

/-- The ideal-power quotient system satisfies the coherent-formal-module conditions along `I`. -/
@[stacks 0880 "ideal-power quotients form a coherent formal module"]
theorem system_mem (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace) :
    IsCoherentFormalModuleSystem I (system I ℱ) := sorry

/-- The coherent formal module obtained by completing `ℱ` along `I`. -/
@[stacks 0880 "completion of a coherent module"]
def obj (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace) :
    CoherentFormalModules X I :=
  ⟨system I ℱ, system_mem I ℱ⟩

/-- A morphism of coherent modules induces a morphism on every completion stage. -/
@[stacks 0880 "morphism on coherent-completion stages"]
def stageMap (I : X.IdealSheafData) {ℱ 𝒢 : RingedSpace.Coh X.toRingedSpace}
    (f : ℱ ⟶ 𝒢) (n : ℕ) : stage I ℱ n ⟶ stage I 𝒢 n :=
  ObjectProperty.homMk
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.map.{u, u, u}
      I.toSubobject f.hom n)

/-- Stage maps commute with the successor transitions of coherent completion. -/
@[stacks 0880 "naturality of coherent-completion stage maps"]
theorem stageMap_naturality (I : X.IdealSheafData)
    {ℱ 𝒢 : RingedSpace.Coh X.toRingedSpace} (f : ℱ ⟶ 𝒢) (n : ℕ) :
    step I ℱ n ≫ stageMap I f n = stageMap I f (n + 1) ≫ step I 𝒢 n := sorry
/-- Stage maps satisfy the successor equation in the form used by `NatTrans.ofOpSequence`. -/
@[stacks 0880 "successor naturality of coherent-completion system maps"]
theorem systemMap_naturality (I : X.IdealSheafData)
    {ℱ 𝒢 : RingedSpace.Coh X.toRingedSpace} (f : ℱ ⟶ 𝒢) (n : ℕ) :
    (system I ℱ).map (homOfLE (Nat.le_add_right n 1)).op ≫ stageMap I f n =
      stageMap I f (n + 1) ≫
        (system I 𝒢).map (homOfLE (Nat.le_add_right n 1)).op := sorry


/-- The natural transformation between ideal-power quotient systems induced by `f`. -/
@[stacks 0880 "morphism of coherent-completion systems"]
def systemMap (I : X.IdealSheafData) {ℱ 𝒢 : RingedSpace.Coh X.toRingedSpace}
    (f : ℱ ⟶ 𝒢) : system I ℱ ⟶ system I 𝒢 :=
  NatTrans.ofOpSequence (stageMap I f) (systemMap_naturality I f)

/-- The morphism between coherent formal completions induced by `f`. -/
@[stacks 0880 "morphism of coherent completions"]
def map (I : X.IdealSheafData) {ℱ 𝒢 : RingedSpace.Coh X.toRingedSpace}
    (f : ℱ ⟶ 𝒢) : obj I ℱ ⟶ obj I 𝒢 :=
  ObjectProperty.homMk (systemMap I f)

/-- Completion sends identity morphisms to identity morphisms. -/
@[stacks 0880 "identity law for coherent completion"]
theorem map_id (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace) :
    map I (𝟙 ℱ) = 𝟙 (obj I ℱ) := sorry

/-- Completion sends composites to composites. -/
@[stacks 0880 "composition law for coherent completion"]
theorem map_comp (I : X.IdealSheafData) {ℱ 𝒢 ℋ : RingedSpace.Coh X.toRingedSpace}
    (f : ℱ ⟶ 𝒢) (g : 𝒢 ⟶ ℋ) :
    map I (f ≫ g) = map I f ≫ map I g := sorry

/-- The canonical completion functor
`Coh(𝒪_X) ⥤ Coh(X, I)`, sending `ℱ` to the system `n ↦ ℱ / I ^ n ℱ`. -/
@[stacks 0880 "canonical coherent completion functor"]
def functor (I : X.IdealSheafData) :
    RingedSpace.Coh X.toRingedSpace ⥤ CoherentFormalModules X I where
  obj := obj I
  map := map I
  map_id := map_id I
  map_comp := map_comp I

/-- Stage `n` of the canonical completion functor is the canonical ideal-power quotient. -/
@[stacks 0880 "stage comparison for the canonical completion functor"]
def stageIso (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ) :
    SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        I.toSubobject ℱ.obj n ≅
      ((((functor I).obj ℱ).obj).obj (op n)).obj :=
  Iso.refl _

/-- The canonical stage comparisons commute with morphisms of coherent modules. -/
@[stacks 0880 "naturality of the canonical completion stage comparison"]
theorem stageIso_naturality (I : X.IdealSheafData)
    {ℱ 𝒢 : RingedSpace.Coh X.toRingedSpace} (f : ℱ ⟶ 𝒢) (n : ℕ) :
    SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.map.{u, u, u}
        I.toSubobject f.hom n ≫ (stageIso I 𝒢 n).hom =
      (stageIso I ℱ n).hom ≫ (((functor I).map f).hom.app (op n)).hom := sorry

/-- The canonical stage comparisons commute with completion transitions. -/
@[stacks 0880 "transition compatibility of the canonical completion stage comparison"]
theorem stageIso_transition (I : X.IdealSheafData)
    (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ) :
    (stageIso I ℱ (n + 1)).hom ≫ ((((functor I).obj ℱ).obj).stepMap n).hom =
      SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.step.{u, u, u}
          I.toSubobject ℱ.obj n ≫ (stageIso I ℱ n).hom := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion

/-- A completion presentation consists of a functor together with specified, natural
identifications of all its stages with the canonical ideal-power quotients. -/
@[stacks 0880 "coherent completion presentation"]
structure CoherentCompletionFunctor (X : Scheme.{u}) (I : X.IdealSheafData)
    extends RingedSpace.Coh X.toRingedSpace ⥤ Scheme.CoherentFormalModules X I where
  /-- The quotient module sheaf `ℱ / I ^ n ℱ` is the `n`th stage of the presented completion. -/
  stagePowerQuotientIso :
    ∀ (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ),
      SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
          I.toSubobject ℱ.obj n ≅
        ((((toFunctor.obj ℱ).obj).obj (op n)).obj)
  /-- The stage identifications commute with morphisms of coherent modules. -/
  stagePowerQuotientIso_naturality :
    ∀ {ℱ 𝒢 : RingedSpace.Coh X.toRingedSpace} (f : ℱ ⟶ 𝒢) (n : ℕ),
      SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.map.{u, u, u}
          I.toSubobject f.hom n ≫ (stagePowerQuotientIso 𝒢 n).hom =
        (stagePowerQuotientIso ℱ n).hom ≫ ((toFunctor.map f).hom.app (op n)).hom
  /-- The stage identifications commute with inverse-system transitions. -/
  stagePowerQuotientIso_transition :
    ∀ (ℱ : RingedSpace.Coh X.toRingedSpace) (n : ℕ),
      (stagePowerQuotientIso ℱ (n + 1)).hom ≫ (((toFunctor.obj ℱ).obj).stepMap n).hom =
        SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.step.{u, u, u}
            I.toSubobject ℱ.obj n ≫ (stagePowerQuotientIso ℱ n).hom

namespace CoherentCompletionFunctor

/-- The canonical completion presentation, built from the explicit ideal-power quotient functor. -/
@[stacks 0880 "canonical coherent completion presentation"]
def canonical (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) :
    CoherentCompletionFunctor X I where
  toFunctor := Scheme.CoherentCompletion.functor I
  stagePowerQuotientIso := Scheme.CoherentCompletion.stageIso I
  stagePowerQuotientIso_naturality := Scheme.CoherentCompletion.stageIso_naturality I
  stagePowerQuotientIso_transition := Scheme.CoherentCompletion.stageIso_transition I

end CoherentCompletionFunctor
