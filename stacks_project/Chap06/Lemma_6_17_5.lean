module

public import ReasLib.Topology.Sheaves.Types.Sheafification
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u))

/- The source uses the sectionwise notion of injectivity from Definition 6.16.2.  The canonical
site-theoretic owner `Presieve.IsSeparated` and the concrete sheafification unit `ℱ.toSheafify`
therefore give the most literal public statement; the categorical reformulation
`Mono ℱ.toSheafify` remains available through `NatTrans.mono_iff_mono_app` and
`CategoryTheory.mono_iff_injective` without replacing
the source-facing predicate. -/

/- Lemma 6.17.5: a set-valued presheaf on `X` is separated if and only if the canonical map
`ℱ ⟶ ℱ^#` to its sheafification is injective on sections over every open subset. -/
@[stacks 0082]
#check isSeparated_iff_toSheafify_injective ℱ

end TopCat.Presheaf
