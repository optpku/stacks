module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Effaceable

/-!
# Acyclic ambient embeddings for continuous group cohomology

Positive-degree invariants-derived functors are effaced by the existing
functorial injective embedding in all discrete continuous modules. These results
do not assert acyclicity of an associated étale sheaf of such an injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat

noncomputable section

universe u v

namespace AmbientDiscreteCohomology

variable (Λ : Type u) [CommRing Λ]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An ambient injective representation is acyclic for positive-degree continuous cohomology. -/
theorem injective_acyclic (I : DiscreteModuleCat Λ G) [Injective I] (n : ℕ) :
    IsZero ((DiscreteModuleCat.derivedCohomologyFunctor Λ G (n + 1)).obj I) :=
  (DiscreteModuleCat.fixedPointsFunctor Λ G).isZero_rightDerived_obj_injective_succ n I

/-- The specified cofree/coreflection injective target of a discrete representation. -/
def effacingObject (M : DiscreteModuleCat Λ G) : DiscreteModuleCat Λ G :=
  (HasFunctorialInjectives.presentation M).J

/-- The specified ambient embedding, with no requirement that its target be finite. -/
def effacingMap (M : DiscreteModuleCat Λ G) : M ⟶ effacingObject Λ G M :=
  (HasFunctorialInjectives.presentation M).f

/-- The specified ambient embeddings are natural in equivariant coefficient maps. -/
theorem effacingMap_naturality {M N : DiscreteModuleCat Λ G} (f : M ⟶ N) :
    f ≫ effacingMap Λ G N =
      effacingMap Λ G M ≫ HasFunctorialInjectives.map f :=
  (HasFunctorialInjectives.ι (C := DiscreteModuleCat Λ G)).naturality f

/-- The ambient embedding target is injective by the canonical presentation. -/
instance effacingObject_injective (M : DiscreteModuleCat Λ G) :
    Injective (effacingObject Λ G M) :=
  (HasFunctorialInjectives.presentation M).injective

/-- The chosen ambient embedding is monic. -/
instance effacingMap_mono (M : DiscreteModuleCat Λ G) : Mono (effacingMap Λ G M) :=
  (HasFunctorialInjectives.presentation M).mono

/-- The chosen embedding target is acyclic for every positive degree. -/
theorem effacingObject_acyclic (M : DiscreteModuleCat Λ G) (n : ℕ) :
    IsZero ((DiscreteModuleCat.derivedCohomologyFunctor Λ G (n + 1)).obj (effacingObject Λ G M)) :=
  injective_acyclic Λ G (effacingObject Λ G M) n

/-- The actual ambient embedding effaces every positive cohomology map. -/
theorem effacingMap_cohomology (M : DiscreteModuleCat Λ G) (n : ℕ) :
    (DiscreteModuleCat.derivedCohomologyFunctor Λ G (n + 1)).map (effacingMap Λ G M) = 0 :=
  (effacingObject_acyclic Λ G M n).eq_of_tgt _ _

/-- Positive-degree continuous cohomology is effaceable in the ambient category. -/
theorem cohomology_isEffaceable (n : ℕ) : (DiscreteModuleCat.derivedCohomologyFunctor Λ G (n + 1)).IsEffaceable := by
  intro M
  exact ⟨effacingObject Λ G M, effacingMap Λ G M, inferInstance,
    effacingMap_cohomology Λ G M n⟩

end AmbientDiscreteCohomology
