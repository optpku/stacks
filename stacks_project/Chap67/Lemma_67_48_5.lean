module

public import stacks_project.Chap67.Lemma_67_48_5_Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.48.5 (1): if `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism
of algebraic spaces over a scheme `S`, then the canonical factorization through
`Hom.normalization f` is a relative-normalization factorization. -/
@[stacks 0823] #check
  (Hom.isNormalization_normalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      IsNormalization f (Hom.toNormalization f) (Hom.fromNormalization f))

/- Lemma 67.48.5 (2): if `f = g ≫ π` is a factorization of a quasi-compact and
quasi-separated morphism through an integral morphism `π : Z ⟶ Y`, then the unique
comparison `h : Hom.normalization f ⟶ Z` is the relative normalization of `Z` in
the source of `f`. -/
@[stacks 0823] #check
  (Hom.isNormalization_lift :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      (g : X ⟶ Z) (π : Z ⟶ Y) [IsIntegralHom π],
      f = g ≫ π →
        ∀ (h : Hom.normalization f ⟶ Z),
          Hom.toNormalization f ≫ h = g →
            h ≫ π = Hom.fromNormalization f →
              IsNormalization g (Hom.toNormalization f) h)

end AlgebraicGeometry.AlgebraicSpace
