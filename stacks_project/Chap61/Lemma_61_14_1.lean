module

public import ReasLib.AlgebraicGeometry.Sites.Proetale.Hypercovering.Existence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 61.14.1 (1): for every object `U` of the small pro-étale site `X.ProEt`
there exists a hypercovering `K` of `U` whose every degree family is a singleton
weakly contractible object covering `U`. -/
@[stacks 09A1] #check
  (AlgebraicGeometry.Scheme.ProEt.exists_hypercovering_isWeaklyContractibleSingleton :
    ∀ (X : Scheme.{u}) (U : X.ProEt),
      ∃ K : CategoryTheory.Hypercovering.{u} (ProEt.topology X) U,
        (∀ n, Nonempty (K.family n).index) ∧
          (∀ n, Subsingleton (K.family n).index) ∧
            (∀ n i, (ProEt.topology X).IsWeaklyContractible ((K.family n).obj i).left))

/- Lemma 61.14.1 (2): for every quasi-compact and quasi-separated object `U` of
`X.ProEt` there exists a hypercovering `K` of `U` whose every degree family is a
singleton affine weakly contractible object covering `U`. -/
@[stacks 09A1] #check
  (AlgebraicGeometry.Scheme.ProEt.exists_hypercovering_isAffine_isWeaklyContractibleSingleton :
    ∀ (X : Scheme.{u}) (U : X.ProEt)
      [CompactSpace U.left] [QuasiSeparatedSpace U.left],
      ∃ K : CategoryTheory.Hypercovering.{u} (ProEt.topology X) U,
        (∀ n, Nonempty (K.family n).index) ∧
          (∀ n, Subsingleton (K.family n).index) ∧
            (∀ n i,
              IsAffine ((K.family n).obj i).left.left ∧
                (ProEt.topology X).IsWeaklyContractible ((K.family n).obj i).left))
