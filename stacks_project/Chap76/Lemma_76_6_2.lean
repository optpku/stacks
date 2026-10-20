module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Algebra.Etale
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.6.2: Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Let `φ : U ⟶ X` be an étale morphism where `U` is a
scheme. Set `Z_U = U ×_X Z`, which is a locally closed subscheme of `U`. Then
`C_{Z/X,*}|_{Z_U} = C_{Z_U/U,*}` canonically and functorially in `U`. The
identification is the isomorphism `ConormalAlgebra.restrictEtale` of
quasi-coherent `𝒪_{Z_U}`-algebras, with `Z_U` realised as `pullback i φ` and
restriction as `QcAlgebraUnder.pullback` along `Hom.Conormal.toZ`. -/
@[stacks 09RR]
#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.restrictEtale :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
      {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (ConormalAlgebra.total i) ≅
      ConormalAlgebra.total (Hom.Conormal.ι i φ))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.restrictEtale_natural :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
      {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    ∀ {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
      (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ),
    (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).map
          (ConormalAlgebra.restrictEtale i ψ).hom ≫
        ConormalAlgebra.restrictEtaleChartMap i φ ψ f hf =
      (ConormalAlgebra.restrictEtaleToZReassoc i φ ψ f hf).hom ≫
        (ConormalAlgebra.restrictEtale i φ).hom)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.restrictEtalePiece :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
      {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    ∀ n : ℕ, (Modules.pullback (Hom.Conormal.toZ i φ)).obj (ConormalAlgebra.piece i n) ≅
      ConormalAlgebra.piece (Hom.Conormal.ι i φ) n)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.restrictEtale_graded :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
      {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    ∀ n : ℕ, ConormalAlgebra.pullbackDegreeToTotal (Hom.Conormal.toZ i φ) i n ≫
        QcAlgebraUnder.underlyingModuleMap
          ((ConormalAlgebra.pullbackTotalIso (Hom.Conormal.toZ i φ) i).inv ≫
            (ConormalAlgebra.restrictEtale i φ).hom) =
      ConormalAlgebra.mapPiece (IsPullback.of_hasPullback i φ).toCommSq n ≫
        ConormalAlgebra.degreeToTotal (Hom.Conormal.ι i φ) n)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.instIsScheme_space :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
      {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    IsScheme (Hom.Conormal.space i φ))

#check (AlgebraicGeometry.AlgebraicSpace.isImmersion_pullback_snd :
    ∀ {S : Scheme.{u}} {Z X W : AlgebraicSpace S} (i : Z ⟶ X) (φ : W ⟶ X)
      [IsImmersion i] [HasPullback i φ], IsImmersion (pullback.snd i φ))
