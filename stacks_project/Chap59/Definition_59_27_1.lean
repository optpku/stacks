module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale.Family
import StacksCheckRecall

universe u v

/- Definition 59.27.1: An étale covering of a scheme is an indexed family of
  étale morphisms whose images jointly cover the target. -/
@[stacks 03PG] #check (AlgebraicGeometry.Scheme.EtaleCovering.{u, v} :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (ι → CategoryTheory.Over T) → Prop)

#check (AlgebraicGeometry.Scheme.etaleCovering_iff.{u, v} :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (family : ι → CategoryTheory.Over T) →
      AlgebraicGeometry.Scheme.EtaleCovering family ↔
        ((∀ i : ι, AlgebraicGeometry.Etale (family i).hom) ∧
          ∀ x : T, ∃ i, x ∈ Set.range (family i).hom))
