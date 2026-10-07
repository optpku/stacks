module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_10_3
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.27.10 (1): a monomorphism of algebraic spaces is separated. -/
@[stacks 0463] #check
  (Separated.of_mono :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f],
      Separated f)

/-- Lemma 67.27.10 (2): a locally of finite type monomorphism of algebraic
spaces is locally quasi-finite. -/
@[stacks 0463]
instance locallyQuasiFinite_of_locallyOfFiniteType_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] : LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
