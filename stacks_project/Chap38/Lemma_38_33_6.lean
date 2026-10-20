module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.ProperExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/- Lemma 38.33.6: a chosen compactification of a quasi-compact open `V` of a separated
finite-type `S`-scheme `U` admits a `V`-admissible blowup with an open neighborhood on which
the map to `U` extends properly. -/
@[stacks 0F3Z] #check
  (AlgebraicGeometry.Scheme.Compactification.exists_isAdmissibleBlowup_properExtension :
    ∀ {S U : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (f : U ⟶ S) [Scheme.Hom.FiniteType f] [IsSeparated f]
      (V : U.Opens) [QuasiCompact V.ι]
      (P : Of S (Over.mk (V.ι ≫ f))),
      ∃ (Y' : Scheme.{u}) (b : Y' ⟶ P.obj.right.left),
        IsAdmissibleBlowup (Of.ι P).opensRange b ∧
          ∃ (V' : Y'.Opens) (j : V.toScheme ⟶ V'.toScheme)
            (g : V'.toScheme ⟶ U),
            IsOpenImmersion j ∧
              j ≫ V'.ι ≫ b = Of.ι P ∧
                IsProper g ∧
                  j ≫ g = V.ι)

end AlgebraicGeometry.Scheme.Compactification
