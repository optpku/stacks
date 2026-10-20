module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Smooth
public import ReasLib.CategoryTheory.Sites.SheafGroupoid.Quotient
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory

/-!
# Geometric properties of stacks on chosen big fppf sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v uX vX

namespace AlgebraicGeometry.ChosenBigFppfSite

variable (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)

/-- A stack is represented by a sheaf if it is cartesian equivalent over the
site to the discrete Grothendieck construction of that sheaf. -/
def IsRepresentedBySheaf (X : StackOver.{_, _, uX, vX} (𝒮.bigTopology S))
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ E : CartesianBasedFunctor X.p
      (((FiberedCategoryOver.Sets.toGroupoids (𝒮.bigSite S)).obj
        ((FiberedCategoryOver.Sets.ofPresheaf (𝒮.bigSite S)).obj F.obj)).p),
    E.toBasedFunctor.IsEquivalence

/-- Representation by a sheaf is equivalent to existence of a cartesian
equivalence to its discrete Grothendieck construction over the site. -/
theorem isRepresentedBySheaf_iff
    (X : StackOver.{_, _, uX, vX} (𝒮.bigTopology S))
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsRepresentedBySheaf 𝒮 S X F ↔
      ∃ E : CartesianBasedFunctor X.p
          (((FiberedCategoryOver.Sets.toGroupoids (𝒮.bigSite S)).obj
            ((FiberedCategoryOver.Sets.ofPresheaf (𝒮.bigSite S)).obj F.obj)).p),
        E.toBasedFunctor.IsEquivalence := Iff.rfl

variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/-- A stack is algebraic if it admits a smooth internal groupoid
presentation with algebraic-space base, object, and arrow sheaves. -/
def IsAlgebraicStack (X : StackOver.{_, _, uX, vX} (𝒮.bigTopology S)) : Prop :=
  ∃ (B : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (G : SheafGroupoid (𝒮.bigTopology S) B),
    IsAlgebraicSpace B ∧ IsAlgebraicSpace G.U.left ∧ IsAlgebraicSpace G.R.left ∧
      IsSmooth 𝒮 S G.s.left ∧ IsSmooth 𝒮 S G.t.left ∧
        ∃ E : CartesianBasedFunctor G.quotientStack.p X.p,
          E.toBasedFunctor.IsEquivalence

/-- The algebraic property is equivalent to existence of a smooth
algebraic-space groupoid whose actual quotient stack is cartesian equivalent
to the given stack over the site. -/
theorem isAlgebraicStack_iff (X : StackOver.{_, _, uX, vX} (𝒮.bigTopology S)) :
    IsAlgebraicStack 𝒮 S X ↔
      ∃ (B : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (G : SheafGroupoid (𝒮.bigTopology S) B),
        IsAlgebraicSpace B ∧ IsAlgebraicSpace G.U.left ∧ IsAlgebraicSpace G.R.left ∧
          IsSmooth 𝒮 S G.s.left ∧ IsSmooth 𝒮 S G.t.left ∧
            ∃ E : CartesianBasedFunctor G.quotientStack.p X.p,
              E.toBasedFunctor.IsEquivalence := Iff.rfl

/-- A stack is Deligne–Mumford if it admits an étale internal groupoid
presentation with algebraic-space base, object, and arrow sheaves. -/
def IsDeligneMumfordStack (X : StackOver.{_, _, uX, vX} (𝒮.bigTopology S)) : Prop :=
  ∃ (B : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (G : SheafGroupoid (𝒮.bigTopology S) B),
    IsAlgebraicSpace B ∧ IsAlgebraicSpace G.U.left ∧ IsAlgebraicSpace G.R.left ∧
      IsEtale G.s.left ∧ IsEtale G.t.left ∧
        ∃ E : CartesianBasedFunctor G.quotientStack.p X.p,
          E.toBasedFunctor.IsEquivalence

/-- The Deligne–Mumford property is equivalent to existence of an étale
algebraic-space groupoid whose actual quotient stack is cartesian equivalent
to the given stack over the site. -/
theorem isDeligneMumfordStack_iff (X : StackOver.{_, _, uX, vX} (𝒮.bigTopology S)) :
    IsDeligneMumfordStack 𝒮 S X ↔
      ∃ (B : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (G : SheafGroupoid (𝒮.bigTopology S) B),
        IsAlgebraicSpace B ∧ IsAlgebraicSpace G.U.left ∧ IsAlgebraicSpace G.R.left ∧
          IsEtale G.s.left ∧ IsEtale G.t.left ∧
            ∃ E : CartesianBasedFunctor G.quotientStack.p X.p,
              E.toBasedFunctor.IsEquivalence := Iff.rfl

end AlgebraicGeometry.ChosenBigFppfSite
