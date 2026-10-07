module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Over
public import stacks_project.Chap94.Definition_94_12_1_Representable

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

/-- `associatedTopology` is the topology inherited along the projection from the
big `τ`-site of `S`. -/
theorem associatedTopology_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    X.associatedTopology τ = X.p.inheritedTopology (StandardTopology.overTopology τ S) :=
  sorry

/-- The associated Zariski site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev zariskiTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.zariski

/-- The associated Zariski topology is `associatedTopology` at
`StandardTopology.zariski`. -/
theorem zariskiTopology_eq (X : GroupoidsOver S) :
    X.zariskiTopology = X.associatedTopology StandardTopology.zariski :=
  sorry

/-- The associated étale site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev etaleTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.etale

/-- The associated étale topology is `associatedTopology` at
`StandardTopology.etale`. -/
theorem etaleTopology_eq (X : GroupoidsOver S) :
    X.etaleTopology = X.associatedTopology StandardTopology.etale :=
  sorry

/-- The associated smooth site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev smoothTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.smooth

/-- The associated smooth topology is `associatedTopology` at
`StandardTopology.smooth`. -/
theorem smoothTopology_eq (X : GroupoidsOver S) :
    X.smoothTopology = X.associatedTopology StandardTopology.smooth :=
  sorry

/-- The associated syntomic site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev syntomicTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.syntomic

/-- The associated syntomic topology is `associatedTopology` at
`StandardTopology.syntomic`. -/
theorem syntomicTopology_eq (X : GroupoidsOver S) :
    X.syntomicTopology = X.associatedTopology StandardTopology.syntomic :=
  sorry

/-- The associated fppf site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev fppfTopology (X : GroupoidsOver S) : GrothendieckTopology X.total :=
  X.associatedTopology StandardTopology.fppf

/-- The associated fppf topology is `associatedTopology` at
`StandardTopology.fppf`. -/
theorem fppfTopology_eq (X : GroupoidsOver S) :
    X.fppfTopology = X.associatedTopology StandardTopology.fppf :=
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
