module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.27.10: a locally of finite type monomorphism of algebraic spaces is
separated and locally quasi-finite. -/
@[stacks 0463] #check
  (AlgebraicGeometry.AlgebraicSpace.separated_and_locallyQuasiFinite_of_locallyOfFiniteType_of_mono :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f] [Mono f],
      AlgebraicGeometry.AlgebraicSpace.Separated f ∧
        AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite f)
