module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Qcqs.Projective
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Qcqs.Refinements
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 32.12.2 (1): the morphism from a qcqs Chow modification to the original scheme is
H-projective. -/
@[stacks 0GII] #check (AlgebraicGeometry.ChowLemmaQcqsModification.hProjective :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} (M : ChowLemmaQcqsModification f), HProjective M.π)

/- Remark 32.12.2 (2): a qcqs Chow modification can be chosen with reduced source under the
hypotheses of Chow's lemma. -/
@[stacks 0GII] #check (AlgebraicGeometry.ChowLemmaQcqsModification.exists_isReduced :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f],
    ∃ M : ChowLemmaQcqsModification f, IsReduced M.X')

/- Remark 32.12.2 (3): a qcqs Chow modification can be chosen so that its morphism to the
original scheme is of finite presentation under the hypotheses of Chow's lemma. -/
@[stacks 0GII] #check (AlgebraicGeometry.ChowLemmaQcqsModification.exists_finitePresentation :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f],
    ∃ M : ChowLemmaQcqsModification f, Scheme.Hom.FinitePresentation M.π)
