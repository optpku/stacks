module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.44.2: for a field extension `k'/k`, the degree of a finite locally free module of
constant rank on a proper scheme of dimension at most one is unchanged by base change to `k'`. -/
@[stacks 0B59] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_eq_baseChange_of_fieldExtension :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
      {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f]
      (hdim : topologicalKrullDim X ≤ 1)
      (ℰ : X.Modules) [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ],
      AlgebraicGeometry.Scheme.Modules.curveDegree f hdim ℰ n =
        AlgebraicGeometry.Scheme.Modules.curveDegree
          (AlgebraicGeometry.FieldExtension.toBase k k' f)
          (AlgebraicGeometry.FieldExtension.topologicalKrullDim_baseChange_le_one f hdim)
          (AlgebraicGeometry.Scheme.Modules.FieldExtension.baseChange k k' f ℰ) n)
