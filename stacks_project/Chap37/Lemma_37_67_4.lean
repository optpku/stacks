module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.MorphismProperties
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.67.4 (1): the pushout of an admissible span of separated schemes is separated. -/
@[stacks 0E26] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instIsSeparated :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j]
      [X.left.IsSeparated] [Y.left.IsSeparated],
      (pushout i.left j.left).IsSeparated)

/- Lemma 37.67.4 (2): the canonical pushout structure morphism is separated when the
two original structure morphisms are separated. -/
@[stacks 0E26] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instToBaseIsSeparated :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j]
      [AlgebraicGeometry.IsSeparated X.hom] [AlgebraicGeometry.IsSeparated Y.hom],
      AlgebraicGeometry.IsSeparated
        (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.toBase i j))

/- Lemma 37.67.4 (3): the pushout of an admissible span of quasi-separated schemes is
quasi-separated. -/
@[stacks 0E26] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instQuasiSeparatedSpace :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j]
      [QuasiSeparatedSpace X.left] [QuasiSeparatedSpace Y.left],
      QuasiSeparatedSpace (pushout i.left j.left : AlgebraicGeometry.Scheme.{u}))

/- Lemma 37.67.4 (4): the canonical pushout structure morphism is quasi-separated when
the two original structure morphisms are quasi-separated. -/
@[stacks 0E26] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instToBaseQuasiSeparated :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j]
      [AlgebraicGeometry.QuasiSeparated X.hom] [AlgebraicGeometry.QuasiSeparated Y.hom],
      AlgebraicGeometry.QuasiSeparated
        (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.toBase i j))
