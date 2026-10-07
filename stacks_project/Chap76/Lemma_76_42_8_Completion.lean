module

public import stacks_project.Chap76.Lemma_76_42_8_FormalModules

/-!
# Completion of coherent modules on algebraic spaces

The completion functor `Coh(𝒪_X) ⥤ Coh(X, I)` sends a coherent module `F` to
the inverse system `n ↦ F / I^n F`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The successor `I^{n+1} F ⟶ F` composed with the projection onto `F / I^n F`
is zero. -/
theorem powerQuotientStep_comp_zero (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) :
    (Modules.idealPowerProductSubobject I F (n + 1)).arrow ≫
        Modules.powerQuotient.projection I F n = 0 :=
  sorry

/-- The transition `F / I^{n+1} F ⟶ F / I^n F` induced by the identity of `F`. -/
noncomputable def powerQuotientStep (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) :
    Modules.powerQuotient I F (n + 1) ⟶ Modules.powerQuotient I F n :=
  cokernel.desc
    (Modules.idealPowerProductSubobject I F (n + 1)).arrow
    (Modules.powerQuotient.projection I F n)
    (powerQuotientStep_comp_zero I F n)

/-- A morphism of modules composed with the quotient projection of the target
vanishes on `I^n` of the source. -/
theorem powerQuotientMap_comp_zero (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    (Modules.idealPowerProductSubobject I F n).arrow ≫
        (f ≫ Modules.powerQuotient.projection I G n) = 0 :=
  sorry

/-- A morphism of modules induces a morphism of their `I^n`-quotients. -/
noncomputable def powerQuotientMap (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    Modules.powerQuotient I F n ⟶ Modules.powerQuotient I G n :=
  cokernel.desc
    (Modules.idealPowerProductSubobject I F n).arrow
    (f ≫ Modules.powerQuotient.projection I G n)
    (powerQuotientMap_comp_zero I f n)

variable [IsNoetherian X]

/-- Every ideal-power quotient of a coherent module on a Noetherian algebraic
space is coherent. -/
theorem stage_isCoherent (I : IdealSubobject X) (ℱ : Coh X) (n : ℕ) :
    (Modules.powerQuotient I ℱ.obj n).IsCoherent :=
  sorry

/-- Stage `n` of coherent completion, as an object of the coherent-module
category. -/
noncomputable def stage (I : IdealSubobject X) (ℱ : Coh X) (n : ℕ) : Coh X :=
  ⟨Modules.powerQuotient I ℱ.obj n, stage_isCoherent I ℱ n⟩

/-- The transition `F / I^{n+1} F ⟶ F / I^n F` in coherent modules. -/
noncomputable def step (I : IdealSubobject X) (ℱ : Coh X) (n : ℕ) :
    stage I ℱ (n + 1) ⟶ stage I ℱ n :=
  ObjectProperty.homMk (powerQuotientStep I ℱ.obj n)

/-- The explicit inverse system `n ↦ F / I^n F` of coherent modules. -/
noncomputable def system (I : IdealSubobject X) (ℱ : Coh X) :
    SequentialInverseSystem (Coh X) :=
  Functor.ofOpSequence (step I ℱ)

/-- The ideal-power quotient system satisfies the coherent-formal-module
conditions along `I`. -/
theorem system_mem (I : IdealSubobject X) (ℱ : Coh X) :
    IsCoherentFormalModuleSystem I (system I ℱ) :=
  sorry

/-- The coherent formal module obtained by completing `F` along `I`. -/
noncomputable def obj (I : IdealSubobject X) (ℱ : Coh X) :
    CoherentFormalModules X I :=
  ⟨system I ℱ, system_mem I ℱ⟩

/-- A morphism of coherent modules induces a morphism on every completion
stage. -/
noncomputable def stageMap (I : IdealSubobject X) {ℱ 𝒢 : Coh X} (f : ℱ ⟶ 𝒢)
    (n : ℕ) : stage I ℱ n ⟶ stage I 𝒢 n :=
  ObjectProperty.homMk (powerQuotientMap I f.hom n)

/-- Stage maps satisfy the successor equation used by `NatTrans.ofOpSequence`. -/
theorem systemMap_naturality (I : IdealSubobject X) {ℱ 𝒢 : Coh X} (f : ℱ ⟶ 𝒢)
    (n : ℕ) :
    (system I ℱ).map (homOfLE (Nat.le_add_right n 1)).op ≫ stageMap I f n =
      stageMap I f (n + 1) ≫
        (system I 𝒢).map (homOfLE (Nat.le_add_right n 1)).op :=
  sorry

/-- The natural transformation between ideal-power quotient systems induced by
`f`. -/
noncomputable def systemMap (I : IdealSubobject X) {ℱ 𝒢 : Coh X} (f : ℱ ⟶ 𝒢) :
    system I ℱ ⟶ system I 𝒢 :=
  NatTrans.ofOpSequence (stageMap I f) (systemMap_naturality I f)

/-- The morphism between coherent formal completions induced by `f`. -/
noncomputable def map (I : IdealSubobject X) {ℱ 𝒢 : Coh X} (f : ℱ ⟶ 𝒢) :
    obj I ℱ ⟶ obj I 𝒢 :=
  ObjectProperty.homMk (systemMap I f)

/-- Completion sends identity morphisms to identity morphisms. -/
theorem map_id (I : IdealSubobject X) (ℱ : Coh X) :
    map I (𝟙 ℱ) = 𝟙 (obj I ℱ) :=
  sorry

/-- Completion sends composites to composites. -/
theorem map_comp (I : IdealSubobject X) {ℱ 𝒢 ℋ : Coh X} (f : ℱ ⟶ 𝒢)
    (g : 𝒢 ⟶ ℋ) : map I (f ≫ g) = map I f ≫ map I g :=
  sorry

/-- The canonical completion functor `Coh(𝒪_X) ⥤ Coh(X, I)`, sending `F` to the
system `n ↦ F / I^n F`. -/
noncomputable def functor (I : IdealSubobject X) :
    Coh X ⥤ CoherentFormalModules X I where
  obj := obj I
  map := map I
  map_id := map_id I
  map_comp := map_comp I

/-- Stage `n` of the canonical completion functor is the canonical ideal-power
quotient. -/
noncomputable def stageIso (I : IdealSubobject X) (ℱ : Coh X) (n : ℕ) :
    Modules.powerQuotient I ℱ.obj n ≅
      ((((functor I).obj ℱ).obj).obj (op n)).obj :=
  Iso.refl _

/-- The canonical stage comparisons commute with morphisms of coherent
modules. -/
theorem stageIso_naturality (I : IdealSubobject X) {ℱ 𝒢 : Coh X} (f : ℱ ⟶ 𝒢)
    (n : ℕ) :
    powerQuotientMap I f.hom n ≫ (stageIso I 𝒢 n).hom =
      (stageIso I ℱ n).hom ≫ (((functor I).map f).hom.app (op n)).hom :=
  sorry

/-- The canonical stage comparisons commute with completion transitions. -/
theorem stageIso_transition (I : IdealSubobject X) (ℱ : Coh X) (n : ℕ) :
    (stageIso I ℱ (n + 1)).hom ≫ ((((functor I).obj ℱ).obj).stepMap n).hom =
      powerQuotientStep I ℱ.obj n ≫ (stageIso I ℱ n).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

namespace AlgebraicGeometry.AlgebraicSpace

/-- A completion presentation consists of a functor together with specified,
natural identifications of all its stages with the canonical ideal-power
quotients. -/
structure CoherentCompletionFunctor {S : Scheme.{u}} (X : AlgebraicSpace S)
    (I : IdealSubobject X) extends Coh X ⥤ CoherentFormalModules X I where
  /-- The quotient module `F / I^n F` is the `n`th stage of the presented
  completion. -/
  stagePowerQuotientIso :
    ∀ (ℱ : Coh X) (n : ℕ),
      Modules.powerQuotient I ℱ.obj n ≅
        ((((toFunctor.obj ℱ).obj).obj (op n)).obj)
  /-- The stage identifications commute with morphisms of coherent modules. -/
  stagePowerQuotientIso_naturality :
    ∀ {ℱ 𝒢 : Coh X} (f : ℱ ⟶ 𝒢) (n : ℕ),
      CoherentCompletion.powerQuotientMap I f.hom n ≫
          (stagePowerQuotientIso 𝒢 n).hom =
        (stagePowerQuotientIso ℱ n).hom ≫
          ((toFunctor.map f).hom.app (op n)).hom
  /-- The stage identifications commute with inverse-system transitions. -/
  stagePowerQuotientIso_transition :
    ∀ (ℱ : Coh X) (n : ℕ),
      (stagePowerQuotientIso ℱ (n + 1)).hom ≫
          (((toFunctor.obj ℱ).obj).stepMap n).hom =
        CoherentCompletion.powerQuotientStep I ℱ.obj n ≫
          (stagePowerQuotientIso ℱ n).hom

namespace CoherentCompletionFunctor

/-- The canonical completion presentation, built from the explicit ideal-power
quotient functor. -/
noncomputable def canonical {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X] (I : IdealSubobject X) :
    CoherentCompletionFunctor X I where
  toFunctor := CoherentCompletion.functor I
  stagePowerQuotientIso := CoherentCompletion.stageIso I
  stagePowerQuotientIso_naturality := CoherentCompletion.stageIso_naturality I
  stagePowerQuotientIso_transition := CoherentCompletion.stageIso_transition I

end CoherentCompletionFunctor

end AlgebraicGeometry.AlgebraicSpace
