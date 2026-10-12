/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology

/-!
# Full subcategories of associated sites

A full subcategory of the total category of a groupoid fibration may be
stable under morphisms lying over a given class of scheme maps, may contain
a smooth surjective atlas object, and inherits the associated `τ`-topology
along the inclusion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- A full subcategory of the total category of `X` is stable under morphisms
lying over morphisms of schemes in `W` when the source of any such arrow
remains in the subcategory. -/
class IsStableUnderOver (X : GroupoidsOver S) (W : MorphismProperty Scheme.{u})
    (Q : ObjectProperty X.total) : Prop where
  /-- If `φ : x ⟶ x'` lies over a morphism in `W` and `x'` is in `Q`, then `x`
  is in `Q`. -/
  mem_of_liesOver ⦃x x' : X.total⦄ (φ : x ⟶ x') :
    Q x' → W (X.p.map φ).left → Q x

/-- The maximal object property on `X.total` is stable under morphisms lying
over any morphism property of schemes. -/
instance instIsStableUnderOverTop (X : GroupoidsOver S)
    (W : MorphismProperty Scheme.{u}) :
    IsStableUnderOver X W (⊤ : ObjectProperty X.total) :=
  sorry

/-- Stability under morphisms lying over `W` is equivalent to closure of `Q`
under sources of arrows of `X` whose image in `Scheme` lies in `W`. -/
theorem IsStableUnderOver.iff (X : GroupoidsOver S)
    (W : MorphismProperty Scheme.{u}) (Q : ObjectProperty X.total) :
    IsStableUnderOver X W Q ↔
      ∀ ⦃x x' : X.total⦄ (φ : x ⟶ x'), Q x' → W (X.p.map φ).left → Q x :=
  sorry

/-- There exists an object of `Q` whose associated 1-morphism
`(Sch / U)_fppf ⟶ X` is smooth and surjective. -/
def ExistsSmoothSurjectiveObject {X : GroupoidsOver S}
    (Q : ObjectProperty X.total) : Prop :=
  ∃ x : X.total,
    Q x ∧
      Groupoids.Hom.Smooth
          (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) ∧
        Groupoids.Hom.Surjective
          (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x)))

/-- Unfolding of `ExistsSmoothSurjectiveObject` as an object of `Q` whose
Yoneda representative is a smooth surjective 1-morphism. -/
theorem ExistsSmoothSurjectiveObject.exists_iff {X : GroupoidsOver S}
    (Q : ObjectProperty X.total) :
    ExistsSmoothSurjectiveObject Q ↔
      ∃ x : X.total,
        Q x ∧
          Groupoids.Hom.Smooth
              (YonedaSlice.representative
                (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) ∧
            Groupoids.Hom.Surjective
              (YonedaSlice.representative
                (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) :=
  sorry

/-- The Grothendieck topology on a full subcategory of `X` whose covering
families are the families of morphisms in the subcategory that cover in the
associated `τ`-site of `X`. -/
abbrev subcategoryTopology (X : GroupoidsOver S) (τ : StandardTopology)
    (Q : ObjectProperty X.total) : GrothendieckTopology Q.FullSubcategory :=
  Q.ι.restrictedTopology (X.associatedTopology τ)

/-- `subcategoryTopology X τ Q` is the restricted topology of the associated
`τ`-site of `X` along the inclusion of `Q`. -/
theorem subcategoryTopology_eq (X : GroupoidsOver S) (τ : StandardTopology)
    (Q : ObjectProperty X.total) :
    subcategoryTopology X τ Q =
      Q.ι.restrictedTopology (X.associatedTopology τ) :=
  sorry

/-- A represented family in a full subcategory is a declared covering for the
induced `τ`-site if and only if the image family covers in the associated
`τ`-site of `X`. This is membership in the comap precoverage generating
`subcategoryTopology`, not sieve membership in the saturated restricted
topology. -/
theorem ofArrows_mem_subcategoryTopology_iff (X : GroupoidsOver S)
    (τ : StandardTopology) (Q : ObjectProperty X.total)
    {x : Q.FullSubcategory} {ι : Type w} (Y : ι → Q.FullSubcategory)
    (f : ∀ i, Y i ⟶ x) :
    Presieve.ofArrows Y f ∈
        ((X.associatedTopology τ).toPrecoverage.comap Q.ι) x ↔
      Sieve.generate
          (Presieve.ofArrows (fun i ↦ Q.ι.obj (Y i)) (fun i ↦ Q.ι.map (f i))) ∈
        X.associatedTopology τ (Q.ι.obj x) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
