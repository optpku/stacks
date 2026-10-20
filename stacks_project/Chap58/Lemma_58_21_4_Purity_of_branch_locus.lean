module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Purity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

/- Lemma 58.21.4 (Purity of branch locus) -/
@[stacks 0BMB]
#check (AlgebraicGeometry.Scheme.Hom.etaleAt_of_unramifiedAt_codimOne_specializations :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (x : X) (hX : X.isNormalAt x)
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f.base x)))
    (hqf : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f.base x)))
    (hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → f.UnramifiedAt x'),
    f.EtaleAt x)
