module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import StacksCheckRecall

/-!
# A colimit that does not preserve monomorphisms

@stack 00DC

Example 10.8.9 uses the walking span to give an objectwise-injective map of module diagrams whose
map on colimits is not injective. The two diagrams and their natural transformation are retained
as concrete data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The zero map from the source vertex to either copy of `Z`. -/
abbrev forkZeroToInt : PUnit →ₗ[ℤ] ℤ := 0

/-- The identity map used by both arrows of the target span. -/
abbrev forkIntId : ℤ →ₗ[ℤ] ℤ := LinearMap.id

/-- The source system `(0, Z, Z, 0, 0)` on the walking span. -/
def forkColimitExactnessSource : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkZeroToInt) (ModuleCat.ofHom forkZeroToInt)

/-- The target system `(Z, Z, Z, 1, 1)` on the walking span. -/
def forkColimitExactnessTarget : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkIntId) (ModuleCat.ofHom forkIntId)

-- Local declaration justification (source-local instance): the zero vertex of the concrete
-- source diagram is `PUnit`; this pins its canonical subsingleton structure while constructing
-- the natural transformation with `spanHomMk`.
private instance : Subsingleton ↑(forkColimitExactnessSource.obj WalkingSpan.zero) := by
  change Subsingleton PUnit
  infer_instance

/-- The objectwise map `(0, Z, Z) -> (Z, Z, Z)` from Example 10.8.9. -/
def forkColimitExactnessHom : forkColimitExactnessSource ⟶ forkColimitExactnessTarget :=
  spanHomMk 0 (𝟙 _) (𝟙 _)

/-- Every component of the counterexample map is a monomorphism. -/
instance forkColimitExactnessHom_app_mono (i : WalkingSpan) :
    Mono (forkColimitExactnessHom.app i) := sorry

/-- The induced map on colimits is not injective. -/
theorem forkColimitExactnessHom_colimit_not_injective :
    ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := sorry

/-- The induced map on colimits is not a monomorphism. -/
theorem forkColimitExactnessHom_colimit_not_mono :
    ¬ Mono (colim.map forkColimitExactnessHom) := by
  intro h
  exact forkColimitExactnessHom_colimit_not_injective
    ((ModuleCat.mono_iff_injective _).1 h)

/-- The natural transformation itself is a monomorphism. -/
theorem forkColimitExactnessHom_mono : Mono forkColimitExactnessHom := by
  exact NatTrans.mono_of_mono_app forkColimitExactnessHom

/-- Example 10.8.9: taking colimits need not preserve monomorphisms for a nondirected diagram. -/
@[stacks 00DC "colimits are not exact for arbitrary diagrams"]
theorem fork_colimit_counterexample_to_exactness :
    Mono forkColimitExactnessHom ∧ ¬ Mono (colim.map forkColimitExactnessHom) :=
  ⟨forkColimitExactnessHom_mono, forkColimitExactnessHom_colimit_not_mono⟩

/-- Pointwise injectivity form of the same counterexample. -/
theorem fork_colimit_counterexample_to_exactness_injective :
    (∀ i : WalkingSpan, Function.Injective (forkColimitExactnessHom.app i).hom) ∧
      ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := by
  refine ⟨fun i ↦ (ModuleCat.mono_iff_injective _).1
    (forkColimitExactnessHom_app_mono i), ?_⟩
  exact forkColimitExactnessHom_colimit_not_injective


#check @span
#check @spanHomMk
#check @colim.map
