module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Perfect
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

section RingCoefficients

variable {Λ : Type u} [Ring Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ Y : Scheme.{u},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]

/- Proposition 64.13.1. Let X be a projective curve over a field k, Λ a finite
ring, and K ∈ D_ctf(X, Λ). Then RΓ(X_k̄, K) ∈ D_perf(Λ).

The constructible Tor-finite category is represented by bounded constructible
complexes with projective geometric stalks. Geometric derived sections are taken
after inverse image along X_k̄ → X. Coefficients may be noncommutative. -/
@[stacks 03TV] #check
  (AlgebraicGeometry.SchemeOverField.isPerfect_geometricRGamma_of_constructibleTorFinite :
    ∀ (X : SchemeOverField k) [Curve X] [Projective X.hom]
      (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite (X := X.left) (Λ := Λ)),
      DerivedCategory.IsPerfect (geometricRGamma X K.obj))

#check
  (AlgebraicGeometry.SchemeOverField.geometricRGamma_homology_finite_of_constructibleTorFinite :
    ∀ (X : SchemeOverField k) [Curve X] [Projective X.hom]
      (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite (X := X.left) (Λ := Λ)),
      ∀ i : ℤ, Module.Finite Λ
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
          (geometricRGamma X K.obj)))

end RingCoefficients

section CommutativeCoefficients

variable {Λ : Type u} [CommRing Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ Y : Scheme.{u},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]

#check
  (AlgebraicGeometry.SchemeOverField.geometricRGamma_hasFiniteTorDimension_of_constructibleTorFinite :
    ∀ (X : SchemeOverField k) [Curve X] [Projective X.hom]
      (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite (X := X.left) (Λ := Λ)),
      CategoryTheory.DerivedCategory.HasFiniteTorDimension Λ (geometricRGamma X K.obj))

end CommutativeCoefficients

end AlgebraicGeometry.SchemeOverField
