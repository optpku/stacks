module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine
public import stacks_project.Chap36.Lemma_36_4_1

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.3.7: for a ring map `φ : A ⟶ B`, so that
`Spec.map φ : Spec B ⟶ Spec A`, the square formed by derived restriction of scalars,
derived pushforward, and the inverse affine derived-global-sections equivalences
`D(B) ≃ D_QCoh(𝒪_(Spec B))` and `D(A) ≃ D_QCoh(𝒪_(Spec A))` commutes up to
natural isomorphism. -/
@[stacks 0DJK] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affinePushforwardSquare_isomorphic :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
      IsIsomorphic
        ((affineGlobalSections B).inv ⋙ pushforward (Spec.map φ))
        (ModuleCat.derivedRestrictionOfScalars φ.hom ⋙
          (affineGlobalSections A).inv))

end AlgebraicGeometry.Scheme.DerivedQCoh
