module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Order.Directed
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import stacks_project.Chap87.Lemma_87_13_1
public import stacks_project.Chap87.Lemma_87_18_1_Colimit
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Ideal
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Points
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Quotient

/-!
# Fundamental systems of weak ideals of definition

A fundamental system of weak ideals of definition on a McQuillan formal
scheme is a family of weak ideals of definition which, on every formal affine
open, is a neighbourhood basis of `0`. Existence of such a family is equivalent
to `h_X` being a directed colimit of schemes along thickenings as in
Lemma 87.13.1.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- A family of ideals of a topological ring is a fundamental system of weak
ideals of definition when each member is a weak ideal of definition and the
family is a neighbourhood basis of `0`. -/
class IsFundamentalSystemOfWeakIdeals {A : Type u} [CommRing A] [TopologicalSpace A]
    {ι : Type u} (I : ι → Ideal A) : Prop where
  /-- Each member is a weak ideal of definition. -/
  isWeak : ∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I i)
  /-- The family is a neighbourhood basis of `0`. -/
  hasBasis : (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A))

/-- Unfolding of `IsFundamentalSystemOfWeakIdeals`. -/
theorem isFundamentalSystemOfWeakIdeals_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] {ι : Type u} (I : ι → Ideal A) :
    IsFundamentalSystemOfWeakIdeals I ↔
      (∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I i)) ∧
        (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A)) :=
  sorry

/-- All weak ideals of definition of a weakly pre-admissible ring form a
fundamental system. -/
instance instIsFundamentalSystemOfWeakIdeals {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsWeaklyPreadmissibleRing A] :
    IsFundamentalSystemOfWeakIdeals
      (fun J : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ↦ J.ideal) :=
  sorry

/-- A fundamental system of weak ideals of definition on a McQuillan formal
scheme. -/
structure FundamentalSystem (X : FormalScheme.{u}) where
  /-- Index type of the family. -/
  ι : Type u
  /-- The family of ideal sheaves. -/
  ideal : ι → IdealSheafData X
  /-- Each member is a weak ideal of definition. -/
  isWeak : ∀ i, IsWeakIdealOfDefinition (ideal i)
  /-- On every formal affine open, the section ideals form a neighbourhood
  basis of `0`. -/
  hasBasis :
    ∀ U : X.affineOpens,
      (nhds (0 : (X.presheaf.obj (op U.1) : Type u))).HasBasis
        (fun _ : ι ↦ True) (fun i ↦ ((ideal i).ideal U : Set _))

/-- The tautological fundamental system of `ofSpf A`, indexed by all weak
ideals of definition of `A`. -/
def FundamentalSystem.ofSpf (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A) :
    FundamentalSystem (FormalScheme.ofSpf A hA) where
  ι := AffineFormalAlgebraicSpace.WeakIdealOfDefinition A
  ideal := IdealSheafData.ofSpf A hA
  isWeak := fun _ ↦ sorry
  hasBasis := sorry

/-- The index type of `FundamentalSystem.ofSpf A hA` is the type of weak
ideals of definition of `A`. -/
theorem FundamentalSystem.ofSpf_ι (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A) :
    (FundamentalSystem.ofSpf A hA).ι =
      AffineFormalAlgebraicSpace.WeakIdealOfDefinition A :=
  sorry

/-- Members of `FundamentalSystem.ofSpf A hA` are the `ofSpf` ideal sheaves. -/
theorem FundamentalSystem.ofSpf_ideal (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A)
    (J : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A) :
    (FundamentalSystem.ofSpf A hA).ideal J = IdealSheafData.ofSpf A hA J :=
  sorry

/-- A family of ideal sheaves packages as a fundamental system iff it is a
ring-level fundamental system on every formal affine open. -/
theorem FundamentalSystem.isFundamentalSystem_iff {X : FormalScheme.{u}}
    {ι : Type u} (I : ι → IdealSheafData X) :
    (∃ (S : FundamentalSystem X) (h : S.ι = ι), S.ideal = h.symm ▸ I) ↔
      ∀ U : X.affineOpens,
        IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U) :=
  sorry

/-- Being a fundamental system of weak ideals of definition may be checked on
the members of an affine open covering. -/
theorem isFundamentalSystem_iff_affineCover {X : FormalScheme.{u}}
    {ι : Type u} (I : ι → IdealSheafData X) (hI : ∀ i, IsWeakIdealOfDefinition (I i))
    {κ : Type u} (𝒰 : κ → X.affineOpens) (hcover : ⨆ j, (𝒰 j).1 = ⊤) :
    (∀ U : X.affineOpens,
        IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U)) ↔
      ∀ j, IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal (𝒰 j)) :=
  sorry


/-- The functor of points `h_X` is a directed colimit of schemes along
thickenings in the sense of Lemma 87.13.1 if and only if `X` admits a
fundamental system of weak ideals of definition. -/
theorem exists_fundamentalSystem_iff_isDirectedColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u})
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    Nonempty (FundamentalSystem X) ↔
      ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D ((sheafOfPoints 𝒮 S).obj X) ∧
          ∀ i : Λ, ∃ Z : Scheme.{u},
            Nonempty (D.obj i ≅ (sheafOfPoints 𝒮 S).obj (ofScheme.obj Z)) :=
  sorry

end AlgebraicGeometry.McQuillan.FormalScheme
