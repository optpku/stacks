module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Opens
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u v

/- Lemma 35.13.6: compatible open subsets on the members of an fpqc covering family
descend to a unique open subset of the target. -/
@[stacks 03N0]
#check
  (AlgebraicGeometry.Scheme.FpqcCovering.existsUnique_open :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v} {family : ι → Over T}
      (hfamily : AlgebraicGeometry.Scheme.FpqcCovering family)
      (W : (i : ι) → ((family i).left).Opens)
      (hcompat : ∀ i j : ι,
        pullback.fst (family i).hom (family j).hom ⁻¹ᵁ W i =
          pullback.snd (family i).hom (family j).hom ⁻¹ᵁ W j),
      ∃! V : T.Opens, ∀ i : ι, W i = (family i).hom ⁻¹ᵁ V)
