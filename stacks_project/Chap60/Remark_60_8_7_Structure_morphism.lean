/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.StructureMorphism
import ReasLib.AlgebraicGeometry.Crystalline.Base
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
variable [HasSheafify
  (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed) (Type (u + 1))]
variable [∀ P : (RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]

/- Remark 60.8.7 (Structure morphism)
In Situation 60.7.5, `S₀ = B.ideal.subscheme`. If `p` is locally nilpotent on `S₀`,
the source obtains `CRIS(S₀/S)` and the commutative diagram of ringed topoi from
Remark 60.8.5. The structure morphism below is defined without this additional
hypothesis, using the cocontinuous functor `(U, T, δ) ↦ U/S`. Local nilpotence on
`B.source` is already part of `B`. The site-functor factorization through `Over X`
and `Over S₀` is stated by `bigStructureFunctor_factorization`; it is distinct
from the contextual ringed-topos diagram. -/
@[stacks 07IE]
#check (AlgebraicGeometry.Scheme.Crystalline.bigStructureMorphism
    B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.source B.sourceToClosed B.prime_nilpotent :
    MorphismOfTopoiIn B.scheme.bigZariskiTopology
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed))

/- The direct image is the cocontinuous sheaf pushforward, by the generic projection API. -/
#check (CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_pushforward
    (bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed) B.scheme.bigZariskiTopology :
    (bigStructureMorphism B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent).pushforward =
      (bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent).sheafPushforwardCocontinuous
        (Type (u + 1))
        (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
          B.source B.sourceToClosed) B.scheme.bigZariskiTopology)

/- The inverse image is the sheafified cocontinuous pullback, by the generic projection API. -/
#check (CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_inverseImage
    (bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed) B.scheme.bigZariskiTopology :
    (bigStructureMorphism B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent).inverseImage =
      (bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent).sheafPullbackCocontinuous
        (Type (u + 1))
        (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
          B.source B.sourceToClosed) B.scheme.bigZariskiTopology)

end AlgebraicGeometry.Scheme.Crystalline

end
