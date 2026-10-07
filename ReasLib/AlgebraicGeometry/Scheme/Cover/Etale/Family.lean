module

public import Mathlib.AlgebraicGeometry.Sites.Etale

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- An indexed family over `T` is an étale covering when its arrows form a
covering presieve for the canonical étale precoverage. -/
abbrev EtaleCovering (family : ι → CategoryTheory.Over T) : Prop :=
  Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
    Scheme.etalePrecoverage.coverings T

/-- An étale covering is characterized by memberwise étaleness and joint
coverage of the target. -/
theorem etaleCovering_iff (family : ι → CategoryTheory.Over T) :
    EtaleCovering family ↔
      (∀ i : ι, Etale (family i).hom) ∧
        ∀ x : T, ∃ i, x ∈ Set.range (family i).hom := sorry

end AlgebraicGeometry.Scheme
