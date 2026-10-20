/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Over
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Associated sites of a category fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` inherits a Grothendieck
topology on its total category from each of the five big sites of `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The Grothendieck topology on the total category of a category fibred in
groupoids over `(Sch/S)_fppf`, inherited from the big `τ`-site of `S`. -/
abbrev associatedTopology (X : GroupoidsOver S) (τ : StandardTopology) :
    GrothendieckTopology X.total :=
  X.p.inheritedTopology (StandardTopology.overTopology τ S)

/-- The associated Zariski site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev zariskiTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.zariski

/-- The associated étale site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev etaleTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.etale

/-- The associated smooth site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev smoothTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.smooth

/-- The associated syntomic site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev syntomicTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.syntomic

/-- The associated fppf site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev fppfTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.fppf

/-- The Grothendieck topology on the total category of a category fibred in
groupoids, inherited from `(Sch/S)_fppf`. -/
abbrev inheritedFppfTopology (X : GroupoidsOver S) :
    GrothendieckTopology X.total :=
  fppfTopology X

/-- The inherited fppf topology is the topology induced by the projection to the big fppf site. -/
theorem inheritedFppfTopology_eq (X : GroupoidsOver S) :
    inheritedFppfTopology X = X.p.inheritedTopology (Scheme.fppfTopology.over S) :=
  rfl

/-- Every étale covering is an fppf covering on a category fibred in groupoids. -/
theorem etaleTopology_le_fppfTopology (X : GroupoidsOver S) :
    etaleTopology X ≤ fppfTopology X :=
  sorry

/-- For a category fibred in groupoids, a represented family covers in the
associated `τ`-topology if and only if its image covers in the big `τ`-site of
`S`. -/
theorem ofArrows_mem_associatedTopology_iff (X : GroupoidsOver S)
    (τ : StandardTopology) {x : X.total} {ι : Type w} (Y : ι → X.total)
    (f : ∀ i, Y i ⟶ x) :
    Sieve.generate (Presieve.ofArrows Y f) ∈ X.associatedTopology τ x ↔
      Sieve.generate
          (Presieve.ofArrows (fun i ↦ X.p.obj (Y i)) (fun i ↦ X.p.map (f i))) ∈
        StandardTopology.overTopology τ S (X.p.obj x) :=
  sorry

/-- The associated `τ`-site of the canonical slice of `U` is the ordinary big
`τ`-slice site of `U`. -/
theorem associatedTopology_slice (τ : StandardTopology) (U : Over S) :
    (slice U).associatedTopology τ = (StandardTopology.overTopology τ S).over U :=
  sorry

end AlgebraicGeometry.GroupoidsOver
