module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.43.14: if `S` is quasi-compact and quasi-separated and `f : X ⟶ Y` and
`g : Y ⟶ S` are projective morphisms of schemes, then `f ≫ g` is projective. -/
@[stacks 0C4P] #check
  (AlgebraicGeometry.Projective.comp :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S},
      [CompactSpace S] → [QuasiSeparatedSpace S] →
        Projective f → Projective g → Projective (f ≫ g))
