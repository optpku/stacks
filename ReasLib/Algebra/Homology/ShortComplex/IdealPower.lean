/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of short complexes modulo powers of an ideal

@stack 0EGU

This file owns the canonical comparison

`H(S) / I ^ (n + 1) H(S) ⟶ H(S / I ^ (n + 1) S)`

for a short complex `S` of modules.  The zero-based sequential systems use exponent `n + 1`.
The quotient functor, the stage complexes, both towers, and the comparison morphisms are explicit;
the Noetherian finite-term theorem is stated separately from this data.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex.IdealPower

variable {A : Type u} [CommRing A]

/-- Quotienting by `I ^ (n + 1)` as an endofunctor of `ModuleCat A`. -/
@[stacks 0EGU "positive ideal-power quotient endofunctor"]
noncomputable def quotientFunctor (I : Ideal A) (n : ℕ) :
    ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj M := Ideal.PowerQuotient.positiveStage I M n
  map f := Ideal.PowerQuotient.positiveMapApp I f n
  map_id M := Ideal.PowerQuotient.positiveMapApp_id I M n
  map_comp f g := Ideal.PowerQuotient.positiveMapApp_comp I f g n

/-- The positive ideal-power quotient functor maps zero morphisms to zero. -/
@[stacks 0EGU "zero law for the positive ideal-power quotient functor"]
theorem quotientFunctor_map_zero (I : Ideal A) (n : ℕ)
    (M N : ModuleCat.{v} A) :
    (quotientFunctor I n).map (0 : M ⟶ N) = 0 := sorry

/-- The positive ideal-power quotient functor canonically preserves zero morphisms. -/
@[stacks 0EGU "positive ideal-power quotients preserve zero morphisms"]
noncomputable instance quotientFunctor_preservesZeroMorphisms
    (I : Ideal A) (n : ℕ) :
    (quotientFunctor (A := A) I n).PreservesZeroMorphisms where
  map_zero M N := quotientFunctor_map_zero I n M N

/-- Consecutive positive quotient maps are natural in the module. -/
@[stacks 0EGU "naturality of positive ideal-power quotient transitions"]
theorem quotientStep_naturality (I : Ideal A) (n : ℕ)
    {M N : ModuleCat.{v} A} (f : M ⟶ N) :
    Ideal.PowerQuotient.positiveMapApp I f (n + 1) ≫
        Ideal.PowerQuotient.positiveStep I N n =
      Ideal.PowerQuotient.positiveStep I M n ≫
        Ideal.PowerQuotient.positiveMapApp I f n := sorry

/-- The natural transition from quotient exponent `n + 2` to exponent `n + 1`. -/
@[stacks 0EGU "natural transition between positive ideal-power quotient functors"]
noncomputable def quotientStep (I : Ideal A) (n : ℕ) :
    quotientFunctor (A := A) I (n + 1) ⟶ quotientFunctor I n where
  app M := Ideal.PowerQuotient.positiveStep I M n
  naturality _ _ f := quotientStep_naturality I n f

/-- The canonical projection of a module to its quotient by `I ^ (n + 1)`. -/
@[stacks 0EGU "projection to a positive ideal-power quotient"]
noncomputable def quotientProjection (I : Ideal A) (n : ℕ) (M : ModuleCat.{v} A) :
    M ⟶ Ideal.PowerQuotient.positiveStage I M n :=
  ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A M)))

/-- Positive ideal-power quotient projections are natural in the module. -/
@[stacks 0EGU "naturality of positive ideal-power quotient projections"]
theorem quotientProjection_naturality (I : Ideal A) (n : ℕ)
    {M N : ModuleCat.{v} A} (f : M ⟶ N) :
    f ≫ quotientProjection I n N =
      quotientProjection I n M ≫ Ideal.PowerQuotient.positiveMapApp I f n := sorry

/-- The natural projection from a module to its positive ideal-power quotient. -/
@[stacks 0EGU "natural projection to positive ideal-power quotients"]
noncomputable def toQuotient (I : Ideal A) (n : ℕ) :
    Functor.id (ModuleCat.{v} A) ⟶ quotientFunctor I n where
  app M := quotientProjection I n M
  naturality _ _ f := quotientProjection_naturality I n f

/-- The short complex obtained by reducing every term of `S` modulo `I ^ (n + 1)`. -/
@[stacks 0EGU "positive ideal-power quotient stage of a short complex"]
abbrev stage (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ShortComplex (ModuleCat.{v} A) :=
  S.map (quotientFunctor I n)

/-- The transition morphism between consecutive quotient short complexes. -/
@[stacks 0EGU "transition between quotient stages of a short complex"]
noncomputable abbrev step
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    stage S I (n + 1) ⟶ stage S I n :=
  S.mapNatTrans (quotientStep I n)

/-- The homology of the quotient short complex at exponent `n + 1`. -/
@[stacks 0EGU "homology stage of an ideal-power quotient short complex"]
noncomputable abbrev stageHomology
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ModuleCat.{v} A :=
  (stage S I n).homology

/-- The homology map induced by the transition between consecutive quotient complexes. -/
@[stacks 0EGU "transition on ideal-power quotient homology"]
noncomputable abbrev stageHomologyStep
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    stageHomology S I (n + 1) ⟶ stageHomology S I n :=
  ShortComplex.homologyMap (step S I n)

/-- The sequential system `n ↦ H(S / I ^ (n + 1) S)`. -/
@[stacks 0EGU "homology tower of positive ideal-power quotient short complexes"]
noncomputable def tower
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  Functor.ofOpSequence (X := fun n ↦ stageHomology S I n) (stageHomologyStep S I)

/-- The object of the quotient-complex homology tower at index `n`. -/
@[stacks 0EGU "object formula for the ideal-power quotient homology tower"]
theorem tower_obj
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (tower S I).obj (Opposite.op n) = stageHomology S I n := sorry

/-- The successor map of the quotient-complex homology tower. -/
@[stacks 0EGU "successor formula for the ideal-power quotient homology tower"]
theorem tower_stepMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (tower S I).stepMap n = stageHomologyStep S I n := sorry

/-- The positive ideal-power quotient of the ambient homology `H(S)` at stage `n`. -/
@[stacks 0EGU "positive ideal-power quotient of ambient short-complex homology"]
noncomputable abbrev ambientStage
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ModuleCat.{v} A :=
  Ideal.PowerQuotient.positiveStage I S.homology n

/-- The canonical positive ideal-power quotient tower of the ambient homology `H(S)`. -/
@[stacks 0EGU "positive ideal-power quotient tower of ambient homology"]
noncomputable abbrev ambientTower
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  Ideal.PowerQuotient.positiveSystem I S.homology

/-- The object of the ambient-homology quotient tower at index `n`. -/
@[stacks 0EGU "object formula for the ambient homology quotient tower"]
theorem ambientTower_obj
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (ambientTower S I).obj (Opposite.op n) = ambientStage S I n := sorry

/-- The successor map of the ambient-homology quotient tower. -/
@[stacks 0EGU "successor formula for the ambient homology quotient tower"]
theorem ambientTower_stepMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (ambientTower S I).stepMap n =
      Ideal.PowerQuotient.positiveStep I S.homology n := sorry

/-- The map from ambient homology to the homology of the quotient complex. -/
@[stacks 0EGU "ambient homology map to quotient-complex homology"]
noncomputable def toStage
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    S.homology ⟶ stageHomology S I n :=
  ShortComplex.homologyMap (S.mapNatTrans (toQuotient I n))

/-- The map from ambient homology to quotient-complex homology kills
`I ^ (n + 1) H(S)`. -/
@[stacks 0EGU "descent condition for ideal-power quotient homology"]
theorem toStage_pow_le_ker
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A S.homology) ≤
      LinearMap.ker (toStage S I n).hom := sorry

/-- The canonical stage comparison
`H(S) / I ^ (n + 1) H(S) ⟶ H(S / I ^ (n + 1) S)`, explicitly descended by
`Submodule.liftQ`. -/
@[stacks 0EGU "canonical comparison on ideal-power quotient homology stages"]
noncomputable def comparisonApp
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ambientStage S I n ⟶ stageHomology S I n :=
  ModuleCat.ofHom <|
    Submodule.liftQ
      (I ^ (n + 1) • (⊤ : Submodule A S.homology))
      (toStage S I n).hom (toStage_pow_le_ker S I n)

/-- Precomposing the stage comparison with the quotient projection recovers `toStage`. -/
@[stacks 0EGU "stage comparison on ambient homology representatives"]
theorem quotientProjection_comp_comparisonApp
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    quotientProjection I n S.homology ≫ comparisonApp S I n = toStage S I n := sorry

/-- The stage comparisons commute with the explicit positive quotient and homology transitions. -/
@[stacks 0EGU "explicit transition compatibility of the ideal-power homology comparison"]
theorem comparisonApp_step
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    Ideal.PowerQuotient.positiveStep I S.homology n ≫ comparisonApp S I n =
      comparisonApp S I (n + 1) ≫ stageHomologyStep S I n := sorry

/-- The stage comparisons commute with the successor maps of the two inverse systems. -/
@[stacks 0EGU "naturality of the ideal-power homology comparison"]
theorem comparisonApp_naturality
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (ambientTower S I).stepMap n ≫ comparisonApp S I n =
      comparisonApp S I (n + 1) ≫ (tower S I).stepMap n := sorry

/-- The canonical stage comparisons assemble into a morphism from the ambient homology quotient
tower to the quotient-complex homology tower. -/
@[stacks 0EGU "comparison of ideal-power homology towers"]
noncomputable def comparison
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) :
    ambientTower S I ⟶ tower S I :=
  NatTrans.ofOpSequence (comparisonApp S I) (comparisonApp_naturality S I)

/-- The component of the tower comparison at stage `n` is `comparisonApp S I n`. -/
@[stacks 0EGU "component formula for the ideal-power homology tower comparison"]
theorem comparison_app
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (comparison S I).app (Opposite.op n) = comparisonApp S I n := sorry

/-- The canonical comparison between the inverse limits of the two ideal-power homology towers. -/
@[stacks 0EGU "canonical limit comparison for ideal-power homology"]
noncomputable def limitComparison
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) :
    limit (ambientTower S I) ⟶ limit (tower S I) :=
  Limits.lim.map (comparison S I)

/-- Projecting `limitComparison` to stage `n` applies the stage comparison after the ambient
limit projection. -/
@[stacks 0EGU "projection formula for the ideal-power homology limit comparison"]
theorem limitComparison_comp_π
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    limitComparison S I ≫ limit.π (tower S I) (Opposite.op n) =
      limit.π (ambientTower S I) (Opposite.op n) ≫ comparisonApp S I n := sorry

namespace Comparison

/-- A reverse comparison from the homology tower shifted by `c` to the ambient-homology
quotient tower. -/
@[stacks 0EGU "shifted reverse ideal-power homology comparison"]
abbrev Shift
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ) :=
  (tower S I).shift c ⟶ ambientTower S I

/-- The canonical morphism of pro-objects induced by the stage comparisons. -/
@[stacks 0EGU "canonical pro-morphism for ideal-power homology"]
noncomputable def proMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) :
    (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (ambientTower S I) ⟶
      (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (tower S I) :=
  (Pro.SequentialHom.ofNatTrans (comparison S I)).toHom

/-- After the fixed shift `c`, the image of the transition to stage `n` is the image of
the canonical map from ambient homology. -/
@[stacks 0EGU "stabilized image of ideal-power quotient homology"]
def ImageStabilizes
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ) : Prop :=
  imageSubobject ((tower S I).transitionMap (Nat.le_add_left n c)) =
    imageSubobject (toStage S I n)

/-- The kernel of the stage comparison is annihilated by `I ^ c`. -/
@[stacks 0EGU "kernel bound for ideal-power homology comparison"]
def HasKernelBound
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ) : Prop :=
  Module.IsTorsionBySet A (LinearMap.ker (comparisonApp S I n).hom)
    (I ^ c : Ideal A)

/-- The cokernel of the stage comparison is annihilated by `I ^ c`. -/
@[stacks 0EGU "cokernel bound for ideal-power homology comparison"]
def HasCokernelBound
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ) : Prop :=
  Module.IsTorsionBySet A
    (stageHomology S I n ⧸ LinearMap.range (comparisonApp S I n).hom)
    (I ^ c : Ideal A)

/-- One exponent uniformly annihilates the kernels and cokernels of every stage comparison. -/
@[stacks 0EGU "uniform kernel-cokernel bound for ideal-power homology"]
def HasUniformBound
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ) : Prop :=
  ∀ n : ℕ, HasKernelBound S I c n ∧ HasCokernelBound S I c n

/-- The quotient of `toStage S I m` modulo `I ^ (n + 1)`. -/
@[stacks 0EGU "quotient of the ambient-to-stage homology map"]
noncomputable def toStageQuotient
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (m n : ℕ) :
    ambientStage S I n ⟶ Ideal.PowerQuotient.positiveStage I (stageHomology S I m) n :=
  Ideal.PowerQuotient.positiveMapApp I (toStage S I m) n

/-- The shifted reverse comparison agrees on `I ^ c` with direct reduction modulo
`I ^ (n + 1)`. -/
@[stacks 0EGU "power compatibility for shifted ideal-power homology comparison"]
def PowerCompatible
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (β : Shift S I c) (n : ℕ) : Prop :=
  ∀ x : (I ^ c • (⊤ : Submodule A (stageHomology S I (c + n))) :
      Submodule A (stageHomology S I (c + n))),
    (eqToHom (tower_obj S I (c + n)).symm ≫ β.app (Opposite.op n) ≫
        toStageQuotient S I (c + n) n).hom x =
      (quotientProjection I n (stageHomology S I (c + n))).hom x

end Comparison

/-- Finiteness of precisely the three terms of a short complex. -/
@[stacks 0EGU "finite terms of a short complex"]
def FiniteTerms (S : ShortComplex (ModuleCat.{v} A)) : Prop :=
  Module.Finite A S.X₁ ∧ Module.Finite A S.X₂ ∧ Module.Finite A S.X₃

/-- Three inferred finite-module instances imply `FiniteTerms`. -/
@[stacks 0EGU "finite short-complex terms from finite-module instances"]
theorem finiteTerms_of_instances (S : ShortComplex (ModuleCat.{v} A))
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    FiniteTerms S := sorry

/-- Lemma 15.101.1 (0EGU), part (2): over a Noetherian ring, if the three terms of `S` are finite,
the canonical inverse-limit comparison is an isomorphism. -/
@[stacks 0EGU "limit comparison for homology modulo powers of an ideal"]
theorem limitComparison_isIso [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    IsIso (limitComparison S I) := sorry

namespace FiniteTerms

/-- The left term is finite under an explicit `FiniteTerms` hypothesis. -/
@[stacks 0EGU "left-term projection of finite short-complex terms"]
theorem finiteX₁ (S : ShortComplex (ModuleCat.{v} A)) (h : FiniteTerms S) :
    Module.Finite A S.X₁ := sorry

/-- The middle term is finite under an explicit `FiniteTerms` hypothesis. -/
@[stacks 0EGU "middle-term projection of finite short-complex terms"]
theorem finiteX₂ (S : ShortComplex (ModuleCat.{v} A)) (h : FiniteTerms S) :
    Module.Finite A S.X₂ := sorry

/-- The right term is finite under an explicit `FiniteTerms` hypothesis. -/
@[stacks 0EGU "right-term projection of finite short-complex terms"]
theorem finiteX₃ (S : ShortComplex (ModuleCat.{v} A)) (h : FiniteTerms S) :
    Module.Finite A S.X₃ := sorry

/-- Lemma 15.101.1 (0EGU), part (1): the canonical tower comparison has a reverse after one
positive fixed shift, and the two composites are the corresponding transition maps. -/
@[stacks 0EGU "shift inverse for ideal-power homology towers"]
theorem existsShift [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    ∃ c : ℕ, 0 < c ∧ ∃ β : Comparison.Shift S I c,
      Pro.SequentialHom.IsShiftInverse (comparison S I) c β := sorry

/-- The canonical pro-morphism attached to the stage comparison is invertible. -/
@[stacks 0EGU "pro-isomorphism for ideal-power homology towers"]
theorem proMap_isIso [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    IsIso (Comparison.proMap S I) := sorry

/-- Lemma 15.101.1 (0EGU), part (3): the homology tower of the quotient short complexes is
Mittag-Leffler. -/
@[stacks 0EGU "Mittag-Leffler ideal-power homology tower"]
theorem towerIsMittagLeffler [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    (tower S I).IsMittagLeffler := sorry

/-- Lemma 15.101.1 (0EGU), part (4): the images in the quotient-complex homology tower stabilize
uniformly after one positive shift. -/
@[stacks 0EGU "uniform image stabilization for ideal-power homology"]
theorem existsImageStabilization [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, Comparison.ImageStabilizes S I c n := sorry

/-- Lemma 15.101.1 (0EGU), part (5): one positive ideal power uniformly annihilates every
stage-comparison kernel and cokernel. -/
@[stacks 0EGU "uniform annihilation for ideal-power homology comparison"]
theorem existsUniformBound [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    ∃ c : ℕ, 0 < c ∧ Comparison.HasUniformBound S I c := sorry

/-- Lemma 15.101.1 (0EGU), part (6): the shift inverse can be chosen to satisfy the ideal-power
compatibility formula at every stage. -/
@[stacks 0EGU "power-compatible shift inverse for ideal-power homology"]
theorem existsPowerCompatible [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    ∃ c : ℕ, 0 < c ∧ ∃ β : Comparison.Shift S I c,
      Pro.SequentialHom.IsShiftInverse (comparison S I) c β ∧
        ∀ n : ℕ, Comparison.PowerCompatible S I c β n := sorry

/-- Finite terms supplied as a proposition make the canonical limit comparison invertible.
This is the direct consumer API for `FiniteTerms`; callers do not need to rebuild temporary
finite-module instances. -/
@[stacks 0EGU "limit comparison from an explicit finite-terms hypothesis"]
theorem isIso [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    IsIso (limitComparison S I) := sorry

/-- The canonical limit isomorphism obtained from an explicit `FiniteTerms` hypothesis. -/
@[stacks 0EGU "canonical limit isomorphism from an explicit finite-terms hypothesis"]
noncomputable def limitIso [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    limit (ambientTower S I) ≅ limit (tower S I) :=
  @asIso (ModuleCat.{v} A) _ _ _ (limitComparison S I) (isIso S I h)

/-- The forward map of the finite-terms limit isomorphism is the canonical comparison. -/
@[stacks 0EGU "forward map of the finite-terms limit isomorphism"]
theorem limitIso_hom [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (h : FiniteTerms S) :
    (limitIso S I h).hom = limitComparison S I := sorry

end FiniteTerms

/-- The canonical inverse-limit isomorphism associated to `limitComparison`. -/
@[stacks 0EGU "canonical limit isomorphism for ideal-power homology"]
noncomputable def limitIso
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [IsIso (limitComparison S I)] :
    limit (ambientTower S I) ≅ limit (tower S I) :=
  asIso (limitComparison S I)

/-- The canonical limit isomorphism obtained directly from the finite-term comparison theorem.
This explicit bridge keeps callers from rebuilding a temporary `IsIso` instance. -/
@[stacks 0EGU "finite-term canonical limit isomorphism"]
noncomputable def finiteLimitIso [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    limit (ambientTower S I) ≅ limit (tower S I) :=
  FiniteTerms.limitIso S I (finiteTerms_of_instances S)

/-- The finite-module specialization has the canonical limit comparison as its forward map. -/
@[stacks 0EGU "forward map of the finite-module limit isomorphism"]
theorem finiteLimitIso_hom [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    (finiteLimitIso S I).hom = limitComparison S I := sorry

end CategoryTheory.ShortComplex.IdealPower
