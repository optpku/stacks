module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.40.4 (1): quasi-projective morphisms are separated. -/
@[stacks 01VX] #check
  (AlgebraicGeometry.QuasiProjective.isSeparated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.QuasiProjective f],
      AlgebraicGeometry.IsSeparated f)

/- Lemma 29.40.4 (2): quasi-projective morphisms are of finite type. -/
@[stacks 01VX] #check
  (AlgebraicGeometry.QuasiProjective.finiteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.QuasiProjective f],
      AlgebraicGeometry.Scheme.Hom.FiniteType f)

/- Lemma 29.40.4 (3): H-quasi-projective morphisms are separated. -/
@[stacks 01VX] #check
  (AlgebraicGeometry.HQuasiProjective.isSeparated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.HQuasiProjective f],
      AlgebraicGeometry.IsSeparated f)

/- Lemma 29.40.4 (4): H-quasi-projective morphisms are of finite type. -/
@[stacks 01VX] #check
  (AlgebraicGeometry.HQuasiProjective.finiteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.HQuasiProjective f],
      AlgebraicGeometry.Scheme.Hom.FiniteType f)

/- Lemma 29.40.4 (5): locally quasi-projective morphisms are separated. -/
@[stacks 01VX] #check
  (AlgebraicGeometry.LocallyQuasiProjective.isSeparated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.LocallyQuasiProjective f],
      AlgebraicGeometry.IsSeparated f)

/- Lemma 29.40.4 (6): locally quasi-projective morphisms are of finite type. -/
@[stacks 01VX] #check
  (AlgebraicGeometry.LocallyQuasiProjective.finiteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.LocallyQuasiProjective f],
      AlgebraicGeometry.Scheme.Hom.FiniteType f)
