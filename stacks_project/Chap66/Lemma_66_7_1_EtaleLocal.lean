module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Étale-local transfer for algebraic spaces

An étale-local property of schemes transfers from one surjective étale scheme atlas of an
algebraic space to every étale morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale :
  ∀ {S : Scheme.{u}}, ObjectProperty Scheme.{u} → AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.forallEtale :
  ∀ {S : Scheme.{u}}, ObjectProperty Scheme.{u} → AlgebraicSpace S → Prop)

end AlgebraicGeometry.AlgebraicSpace
