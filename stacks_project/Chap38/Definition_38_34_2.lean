module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
import StacksCheckRecall

universe u v

/- Definition 38.34.2: An h covering of a scheme `T` is a family of morphisms
to `T` that are locally of finite presentation and satisfy the equivalent
covering conditions of Lemma 38.34.1. -/
@[stacks 0ETS] #check (AlgebraicGeometry.Scheme.HCovering :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v},
    (ι → CategoryTheory.Over T) → Prop)

#check (AlgebraicGeometry.Scheme.hCovering_iff :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    (family : ι → CategoryTheory.Over T),
    AlgebraicGeometry.Scheme.HCovering family ↔
      (∀ i, AlgebraicGeometry.LocallyOfFinitePresentation (family i).hom) ∧
        AlgebraicGeometry.PhCovering
          (fun i ↦ (family i).left) (fun i ↦ (family i).hom))
