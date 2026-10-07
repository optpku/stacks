module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_FormalScheme
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Neighborhoods
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Spf
import StacksCheckRecall

/-!
# Remark 87.2.3 (McQuillan's variant)

McQuillan's EGA-style variant of formal schemes, based on weakly admissible
topological rings and weak ideals of definition.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalRing

/- Remark 87.2.3 (McQuillan's variant) (1): an admissible topological ring is a
complete separated linearly topologized ring with an ideal of definition, and a
weakly admissible topological ring is a complete separated linearly topologized
ring with a weak ideal of definition: an open ideal of topologically nilpotent
elements. -/
@[stacks 0AI3] #check @IsTopologicallyNilpotent

@[stacks 0AI3] #check @TopologicalRing.Ideal.IsIdealOfDefinition

@[stacks 0AI3] #check @TopologicalRing.IsAdmissibleRing

@[stacks 0AI3] #check @TopologicalRing.Ideal.IsWeakIdealOfDefinition

@[stacks 0AI3] #check @TopologicalRing.IsWeaklyAdmissibleRing

/- Remark 87.2.3 (McQuillan's variant) (2): if `I` is a weak ideal of definition and
`J` is an open ideal, then `I ⊓ J` is a weak ideal of definition. -/
@[stacks 0AI3] #check @TopologicalRing.Ideal.IsWeakIdealOfDefinition.inf_of_isOpen

/- Remark 87.2.3 (McQuillan's variant) (3): the weak ideals of definition form a
fundamental system of open neighbourhoods of `0`. -/
@[stacks 0AI3] #check @TopologicalRing.hasBasis_isWeakIdealOfDefinition

/- Remark 87.2.3 (McQuillan's variant) (4): repeating the Spf construction over weak
ideals of definition yields a larger category of formal schemes, locally modelled
on McQuillan `spf` of a weakly admissible ring. -/
@[stacks 0AI3] #check AlgebraicGeometry.McQuillan.FormalScheme

@[stacks 0AI3] #check AlgebraicGeometry.McQuillan.spf

@[stacks 0AI3] #check AlgebraicGeometry.McQuillan.FormalScheme.ofFormalScheme

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- Remark 87.2.3 (McQuillan's variant) (5): the analogue of Lemma 87.2.1 holds for
McQuillan's larger category. Choose a category of schemes `Sch_α` as in Sets,
Lemma 3.9.2. Morphisms `X ⟶ Y` of McQuillan formal schemes are in bijection with
morphisms of their functors of points on `(Sch_α)ᵒᵖ`, provided the size of `X` is
not too large. -/
@[stacks 0AI3]
theorem functorOfPoints_map_bijective {P : ObjectProperty Scheme.{u}}
    (hP : Scheme.IsSmallBoundClosed P) {X Y : FormalScheme.{u}}
    (hX : ∃ S, P S ∧ X.size ≤ S.size) :
    Function.Bijective
      ((functorOfPoints P).map :
        (X ⟶ Y) → ((functorOfPoints P).obj X ⟶ (functorOfPoints P).obj Y)) :=
  sorry

/-- Remark 87.2.3 (McQuillan's variant) (6): the analogue of Lemma 87.2.2 holds for
McQuillan's larger category. The functor of points of a McQuillan formal scheme
`X` on `Sch_α` is a sheaf for the fpqc topology. -/
@[stacks 0AI3]
theorem functorOfPoints_isSheaf_fpqc {P : ObjectProperty Scheme.{u}}
    (hP : Scheme.IsSmallBoundClosed P) (X : FormalScheme.{u}) :
    Presheaf.IsSheaf (P.ι.restrictedTopology Scheme.fpqcTopology)
      ((functorOfPoints P).obj X) :=
  sorry

end AlgebraicGeometry.McQuillan.FormalScheme
