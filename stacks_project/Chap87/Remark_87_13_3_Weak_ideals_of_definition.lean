module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Ideal
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Points
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Quotient
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_System

/-!
# Remark 87.13.3 (Weak ideals of definition)

Weak ideals of definition on a McQuillan formal scheme, the associated
thickenings of `h_X`, and the criterion for `h_X` to be a directed colimit of
schemes along thickenings.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- Remark 87.13.3 (Weak ideals of definition) (1): an ideal sheaf on a
McQuillan formal scheme `X` is a weak ideal of definition iff for every
affine formal open `U` the ideal of sections is a weak ideal of definition of
the weakly admissible ring `X.presheaf.obj (op U)`. -/
@[stacks 0AIV]
theorem isWeakIdealOfDefinition_affineOpens {X : FormalScheme.{u}}
    (I : IdealSheafData X) :
    IsWeakIdealOfDefinition I ↔
      ∀ U : X.affineOpens,
        TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal U) :=
  sorry

/-- Remark 87.13.3 (Weak ideals of definition) (2): the weak-ideal-of-definition
condition on an ideal sheaf may be checked on the members of an affine open
covering. -/
@[stacks 0AIV]
theorem isWeakIdealOfDefinition_affineCover {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤) :
    IsWeakIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal (𝒰 i)) :=
  sorry

/-- Remark 87.13.3 (Weak ideals of definition) (3): weak ideals of definition
for `X` correspond to thickenings `Z ⟶ h_X` by sending `I` to the scheme
`Z = (X, O_X / I)` with the obvious morphism, and sending a thickening to its
kernel; the two constructions are mutually inverse. -/
@[stacks 0AIV]
theorem weakIdeal_thickening_correspondence
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : FormalScheme.{u}} :
    (∀ (I : IdealSheafData X) [IsWeakIdealOfDefinition I],
      (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor
          (I.toSchemeThickening 𝒮 S) ∧
        IdealSheafData.ker I.quotientι = I) ∧
      ∀ (Z : Scheme.{u}) (i : ofScheme.obj Z ⟶ X),
        (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor
            ((sheafOfPoints 𝒮 S).map i) →
          ∃ (hI : IsWeakIdealOfDefinition (IdealSheafData.ker i))
            (e : @IdealSheafData.quotientScheme _ (IdealSheafData.ker i) hI ≅ Z),
            ofScheme.map e.hom ≫ i =
              @IdealSheafData.quotientι _ (IdealSheafData.ker i) hI :=
  sorry

/-- Remark 87.13.3 (Weak ideals of definition) (4): a family of ideal sheaves
is a fundamental system of weak ideals of definition iff on every affine
formal open the section ideals form a fundamental system of weak ideals of
definition of the section ring. -/
@[stacks 0AIV]
theorem isFundamentalSystem_affineOpens {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) :
    (∃ (S : FundamentalSystem X) (h : S.ι = ι), S.ideal = h.symm ▸ I) ↔
      ∀ U : X.affineOpens,
        IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U) :=
  sorry

/-- Remark 87.13.3 (Weak ideals of definition) (5): the fundamental-system
condition may be checked on the members of an affine open covering. -/
@[stacks 0AIV]
theorem isFundamentalSystem_affineCover {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : ∀ i, IsWeakIdealOfDefinition (I i))
    {κ : Type u} (𝒰 : κ → X.affineOpens) (hcover : ⨆ j, (𝒰 j).1 = ⊤) :
    (∀ U : X.affineOpens,
        IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U)) ↔
      ∀ j, IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal (𝒰 j)) :=
  sorry

/-- Remark 87.13.3 (Weak ideals of definition) (6): the formal algebraic space
`h_X` associated to a McQuillan formal scheme `X` is a colimit of schemes as
in Lemma 87.13.1 if and only if there exists a fundamental system of weak
ideals of definition for `X`. -/
@[stacks 0AIV]
theorem sheafOfPoints_isDirectedColimit_iff_exists_fundamentalSystem
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
