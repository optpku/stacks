module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.CategoryTheory.Sites.BoundedCohomologyBasis
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import stacks_project.Chap85.Example_85_23_2_Basis
public import stacks_project.Chap85.Example_85_23_2_Site
import Mathlib.Tactic.CrossRefAttribute

/-!
# Example 85.23.2

Unbounded cohomological descent data on the locally finite type étale site of an allowed base,
with constant finite coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ] [Finite Λ]
variable [HasWeakSheafify (etaleTopology S) RingCat.{u}]

/-- Example 85.23.2 (1): for a morphism `U ⟶ V` in the locally finite type étale slice, restriction
of étale sheaves of `Λ`-modules sends `A_V = Mod(O_V)` into `A_U = Mod(O_U)`. -/
@[stacks 0DC6]
theorem restriction (hS : IsFiniteEtaleCoefficientBase S)
    (hΛ : orderInvertible S Λ) {U V : locallyOfFiniteTypeOver S} (f : U ⟶ V)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over V)) :
    (⊤ : ObjectProperty (SheafOfModules.{u} ((constantRingSheaf S Λ).over U)))
      ((SheafOfModules.overMap (constantRingSheaf S Λ) f).obj ℱ) :=
  sorry

/-- Example 85.23.2 (2): membership in `A_U = Mod(O_U)` is local for étale coverings of `U`. -/
@[stacks 0DC6]
theorem local_iff (hS : IsFiniteEtaleCoefficientBase S)
    (hΛ : orderInvertible S Λ) {U : locallyOfFiniteTypeOver S}
    {cover : FormalCoproduct.{u} (Over U)}
    (hcover : ((etaleTopology S).over U).CoversTop cover.obj)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over U)) :
    (⊤ : ObjectProperty (SheafOfModules.{u} ((constantRingSheaf S Λ).over U))) ℱ ↔
      ∀ i : cover.I,
        (⊤ : ObjectProperty
            (SheafOfModules.{u} ((constantRingSheaf S Λ).over (cover.obj i).left)))
          ((SheafOfModules.overMap (constantRingSheaf S Λ) (cover.obj i).hom).obj ℱ) :=
  sorry

/-- Example 85.23.2 (3): for `V` quasi-compact, an étale covering by quasi-compact objects, and
every étale sheaf of `Λ`-modules on the slice `C / V`, cohomology of each covering member vanishes
above the Gabber bound `d_V`. -/
@[stacks 0DC6]
theorem higherCohomology_isZero (hS : IsFiniteEtaleCoefficientBase S)
    (hΛ : orderInvertible S Λ) {V : locallyOfFiniteTypeOver S}
    (hV : quasiCompact S V)
    [HasSheafify ((etaleTopology S).over V) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf ((etaleTopology S).over V) AddCommGrpCat.{u})]
    {cover : FormalCoproduct.{u} (Over V)} (hcover : cover ∈ coveringSystem S V)
    (i : cover.I) (p : ℕ) (hp : cohomologyBound V < p)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over V)) :
    IsZero
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf ((constantRingSheaf S Λ).over V)).obj ℱ)
        (cover.obj i) p) :=
  sorry

/-- The weaker Situation 21.25.1 bounded-cohomology basis assembled from the same quasi-compact
objects, Gabber bound, and quasi-compact étale coverings, with vanishing only for global modules. -/
def toBoundedCohomologyBasis (hS : IsFiniteEtaleCoefficientBase S)
    (hΛ : orderInvertible S Λ)
    [HasSheafify (etaleTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (etaleTopology S) AddCommGrpCat.{u})]
    [(etaleTopology S).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    GrothendieckTopology.BoundedCohomologyBasis (constantRingSheaf S Λ) ⊤ where
  basis := quasiCompact S
  hasEnoughObjectsWithProperty := hasEnoughQuasiCompact S
  cohomologyBound := fun {V} _ ↦ cohomologyBound V
  coveringSystem := fun {V} _ ↦ coveringSystem S V
  coveringSystemIsCover := fun {V} _ {cover} hcover ↦ coveringSystem_isCover hcover
  coveringSystemCofinal := fun {V} _ {ι} family hfamily ↦ coveringSystem_cofinal family hfamily
  higherCohomologyIsZero := sorry

end AlgebraicGeometry.Scheme.Etale
