/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Affine
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import stacks_project.Chap96.Definition_96_24_2_Affine

/-!
# Associated affine sites of a category fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` inherits a Grothendieck
topology on `𝒳_affine` from each of the five standard sites `(Aff/S)_τ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The Grothendieck topology on `𝒳_affine` inherited from the affine `τ`-site
of `S`. -/
abbrev associatedAffineTopology (X : GroupoidsOver S) (τ : StandardTopology) :
    GrothendieckTopology (Affine X) :=
  (affineProjection X).inheritedTopology (StandardTopology.Affine.topology τ S)

/-- `associatedAffineTopology` is the topology inherited along `affineProjection`
from `(Aff/S)_τ`. -/
theorem associatedAffineTopology_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    X.associatedAffineTopology τ =
      (affineProjection X).inheritedTopology
        (StandardTopology.Affine.topology τ S) :=
  sorry

/-- The associated affine Zariski site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev affineZariskiTopology (X : GroupoidsOver S) :
    GrothendieckTopology (Affine X) :=
  X.associatedAffineTopology StandardTopology.zariski

/-- The associated affine Zariski topology is `associatedAffineTopology` at
`StandardTopology.zariski`. -/
theorem affineZariskiTopology_eq (X : GroupoidsOver S) :
    X.affineZariskiTopology = X.associatedAffineTopology StandardTopology.zariski :=
  sorry

/-- The associated affine étale site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev affineEtaleTopology (X : GroupoidsOver S) :
    GrothendieckTopology (Affine X) :=
  X.associatedAffineTopology StandardTopology.etale

/-- The associated affine étale topology is `associatedAffineTopology` at
`StandardTopology.etale`. -/
theorem affineEtaleTopology_eq (X : GroupoidsOver S) :
    X.affineEtaleTopology = X.associatedAffineTopology StandardTopology.etale :=
  sorry

/-- The associated affine smooth site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev affineSmoothTopology (X : GroupoidsOver S) :
    GrothendieckTopology (Affine X) :=
  X.associatedAffineTopology StandardTopology.smooth

/-- The associated affine smooth topology is `associatedAffineTopology` at
`StandardTopology.smooth`. -/
theorem affineSmoothTopology_eq (X : GroupoidsOver S) :
    X.affineSmoothTopology = X.associatedAffineTopology StandardTopology.smooth :=
  sorry

/-- The associated affine syntomic site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev affineSyntomicTopology (X : GroupoidsOver S) :
    GrothendieckTopology (Affine X) :=
  X.associatedAffineTopology StandardTopology.syntomic

/-- The associated affine syntomic topology is `associatedAffineTopology` at
`StandardTopology.syntomic`. -/
theorem affineSyntomicTopology_eq (X : GroupoidsOver S) :
    X.affineSyntomicTopology =
      X.associatedAffineTopology StandardTopology.syntomic :=
  sorry

/-- The associated affine fppf site of a category fibred in groupoids over
`(Sch/S)_fppf`. -/
abbrev affineFppfTopology (X : GroupoidsOver S) :
    GrothendieckTopology (Affine X) :=
  X.associatedAffineTopology StandardTopology.fppf

/-- The associated affine fppf topology is `associatedAffineTopology` at
`StandardTopology.fppf`. -/
theorem affineFppfTopology_eq (X : GroupoidsOver S) :
    X.affineFppfTopology = X.associatedAffineTopology StandardTopology.fppf :=
  sorry

/-- For a category fibred in groupoids, a represented family covers in the
associated affine `τ`-topology if and only if its image under `affineProjection`
covers in `(Aff/S)_τ`. -/
theorem ofArrows_mem_associatedAffineTopology_iff (X : GroupoidsOver S)
    (τ : StandardTopology) {x : Affine X} {ι : Type w} (Y : ι → Affine X)
    (f : ∀ i, Y i ⟶ x) :
    Sieve.generate (Presieve.ofArrows Y f) ∈ X.associatedAffineTopology τ x ↔
      Sieve.generate
          (Presieve.ofArrows (fun i ↦ (affineProjection X).obj (Y i))
            (fun i ↦ (affineProjection X).map (f i))) ∈
        StandardTopology.Affine.topology τ S ((affineProjection X).obj x) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
