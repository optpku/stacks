module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.Small
import StacksCheckRecall

/-!
# Lemma 95.8.2

There exists a full subcategory `Spaces_ft,small ⊂ Spaces_ft` whose inclusion is fully
faithful and essentially surjective, and whose restricted projection is a stack over
`(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Lemma 95.8.2: there exists a subcategory `Spaces_ft,small ⊂ Spaces_ft` whose inclusion
functor `P.ι : Spaces_ft,small ⟶ Spaces_ft` is fully faithful (the canonical `Full`/`Faithful`
instances) and essentially surjective, and whose restricted projection
`p_ft,small = P.ι ⋙ (stack S).p` turns `Spaces_ft,small` into a stack over `(Sch/S)_fppf`.
Fiberwise `Small.{u}` is the big-site meaning of `ft,small`, since the ambient fibre is
only `EssentiallySmall.{u}`. -/
@[stacks 04UE] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.exists_smallSubcategory :
    ∀ S : Scheme.{u},
      ∃ P : ObjectProperty (AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.stack S).total,
        P.ι.EssSurj ∧
          IsStack.OnSite (Scheme.fppfTopology.over S)
            (P.ι ⋙ (AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.stack S).p) ∧
          ∀ U : Over S,
            Small.{u} ((P.ι ⋙
              (AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.stack S).p).Fiber U))

-- The ambient fibers satisfy the essential-smallness condition of Remark 8.4.9.
#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.fibers_essentiallySmall :
    ∀ (S : Scheme.{u}) (U : Over S),
      ObjectProperty.EssentiallySmall.{u}
        (⊤ : ObjectProperty ((AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.p S).Fiber U)))
