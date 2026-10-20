module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Nodal
import StacksCheckRecall

/-!
# Nodal curves

There is an open substack 𝒞urves^{nodal} ⊂ 𝒞urves classifying at-worst-nodal
families of curves of relative dimension 1. Its field-valued objects are proper
schemes with at-worst-nodal singularities and dimension one of every irreducible
component.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.18.1: the nodal condition is represented by an open of the base
under every scheme base change. -/
@[stacks 0DSY] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_nodal_open :
  ∀ {S : Scheme.{u}} (P : Obj S),
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      AlgebraicSpace.AtWorstNodal
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ↔
        Set.range T.hom ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.nodal_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    nodal S P ↔ AlgebraicSpace.AtWorstNodal (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.nodal_iff_scheme_components :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    nodal (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∀ Z : irreducibleComponents X.left,
          topologicalKrullDim Z = 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_nodal_iff_scheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1),
    nodal (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        TopologicalSpace.EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
