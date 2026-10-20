module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.Separation
import StacksCheckRecall

/-!
# Lemma 99.11.9

Under the standing hypotheses of Proposition 99.11.8, the diagonal of the
Picard functor `Pic_{X/B}` is representable by immersions, equivalently
`Pic_{X/B} ⟶ B` is locally separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Lemma 99.11.9: with assumptions and notation as in Proposition 99.11.8
(`f : X ⟶ B` flat, of finite presentation, and proper, and `O_T ⟶ f_{T,*} O_{X_T}`
an isomorphism for every scheme `T` over `B`), the diagonal
`Pic_{X/B} ⟶ Pic_{X/B} ×_B Pic_{X/B}` is representable by immersions. In other
words, `Pic_{X/B} ⟶ B` is locally separated. -/
@[stacks 0D2D] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativePicard.locallySeparated :
    ∀ (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
      [Hom.IsIsoBaseChangeStructurePushforward f],
    IsImmersionOnSchemesOver (Limits.diag (picardFunctor f).obj))

/- If the Picard functor is represented by a morphism `π : Y ⟶ B`, then `π` is
locally separated. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.locallySeparated_of_representable :
  ∀ (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π),
    LocallySeparated π)

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
