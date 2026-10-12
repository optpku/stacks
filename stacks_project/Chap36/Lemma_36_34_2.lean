/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PseudoCoherent

@[expose] public section

open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

/- Lemma 36.34.2: for a quasicoherent derived module `K` on standard projective `n`-space over
a commutative ring `A`, the following are equivalent: `K` is pseudo-coherent; tensor-global
sections against every pseudo-coherent object are pseudo-coherent; tensor-global sections against
every perfect object are pseudo-coherent; derived Hom from every perfect object is
pseudo-coherent; and tensor-global sections against `𝒪(d)` are pseudo-coherent for
`d = 0, …, n`. -/
@[stacks 0CSG] #check
  (AlgebraicGeometry.ProjectiveSpace.pseudoCoherent_tfae :
    ∀ (A : Type u) [CommRing A] (n : ℕ)
      (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
        (AlgebraicGeometry.ProjectiveSpace.scheme A n)),
      List.TFAE [
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent K.obj,
        ∀ E : AlgebraicGeometry.RingedSpace.ModuleDerived
            (AlgebraicGeometry.ProjectiveSpace.scheme A n).toRingedSpace,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent E →
            CategoryTheory.DerivedCategory.IsPseudoCoherent
              ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections
                (AlgebraicGeometry.ProjectiveSpace.toSpec A n)).obj (E ⊗ᴸ K.obj)),
        ∀ E : AlgebraicGeometry.RingedSpace.ModuleDerived
            (AlgebraicGeometry.ProjectiveSpace.scheme A n).toRingedSpace,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E →
            CategoryTheory.DerivedCategory.IsPseudoCoherent
              ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections
                (AlgebraicGeometry.ProjectiveSpace.toSpec A n)).obj (E ⊗ᴸ K.obj)),
        ∀ E : AlgebraicGeometry.RingedSpace.ModuleDerived
            (AlgebraicGeometry.ProjectiveSpace.scheme A n).toRingedSpace,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E →
            CategoryTheory.DerivedCategory.IsPseudoCoherent
              (AlgebraicGeometry.ProjectiveSpace.rHom A n E K.obj),
        ∀ d : Fin (n + 1),
          CategoryTheory.DerivedCategory.IsPseudoCoherent
            ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections
              (AlgebraicGeometry.ProjectiveSpace.toSpec A n)).obj
                (K.obj ⊗ᴸ
                  (_root_.DerivedCategory.singleFunctor
                    (AlgebraicGeometry.ProjectiveSpace.scheme A n).Modules 0).obj
                      (AlgebraicGeometry.ProjectiveSpace.twistingSheaf A n (d : ℤ))))
      ])

#check
  (AlgebraicGeometry.ProjectiveSpace.isPseudoCoherent_iff_tensor_pseudoCoherent :
    ∀ (A : Type u) [CommRing A] (n : ℕ)
      (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
        (AlgebraicGeometry.ProjectiveSpace.scheme A n)),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
        ∀ E : AlgebraicGeometry.RingedSpace.ModuleDerived
            (AlgebraicGeometry.ProjectiveSpace.scheme A n).toRingedSpace,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent E →
            CategoryTheory.DerivedCategory.IsPseudoCoherent
              ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections
                (AlgebraicGeometry.ProjectiveSpace.toSpec A n)).obj (E ⊗ᴸ K.obj)))

#check
  (AlgebraicGeometry.ProjectiveSpace.isPseudoCoherent_iff_tensor_perfect :
    ∀ (A : Type u) [CommRing A] (n : ℕ)
      (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
        (AlgebraicGeometry.ProjectiveSpace.scheme A n)),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
        ∀ E : AlgebraicGeometry.RingedSpace.ModuleDerived
            (AlgebraicGeometry.ProjectiveSpace.scheme A n).toRingedSpace,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E →
            CategoryTheory.DerivedCategory.IsPseudoCoherent
              ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections
                (AlgebraicGeometry.ProjectiveSpace.toSpec A n)).obj (E ⊗ᴸ K.obj)))

#check
  (AlgebraicGeometry.ProjectiveSpace.isPseudoCoherent_iff_rHom_perfect :
    ∀ (A : Type u) [CommRing A] (n : ℕ)
      (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
        (AlgebraicGeometry.ProjectiveSpace.scheme A n)),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
        ∀ E : AlgebraicGeometry.RingedSpace.ModuleDerived
            (AlgebraicGeometry.ProjectiveSpace.scheme A n).toRingedSpace,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E →
            CategoryTheory.DerivedCategory.IsPseudoCoherent
              (AlgebraicGeometry.ProjectiveSpace.rHom A n E K.obj))

#check
  (AlgebraicGeometry.ProjectiveSpace.isPseudoCoherent_iff_twists :
    ∀ (A : Type u) [CommRing A] (n : ℕ)
      (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
        (AlgebraicGeometry.ProjectiveSpace.scheme A n)),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
        ∀ d : Fin (n + 1),
          CategoryTheory.DerivedCategory.IsPseudoCoherent
            ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections
              (AlgebraicGeometry.ProjectiveSpace.toSpec A n)).obj
                (K.obj ⊗ᴸ
                  (_root_.DerivedCategory.singleFunctor
                    (AlgebraicGeometry.ProjectiveSpace.scheme A n).Modules 0).obj
                      (AlgebraicGeometry.ProjectiveSpace.twistingSheaf A n (d : ℤ)))))

end
