module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Composition

@[expose] public section

open CategoryTheory

universe u

/- Lemma 27.18.2
For composable maps of graded algebras, the induced relative-projective-spectrum map has the
inverse-image composite domain, the restricted composite morphism, and the composite degreewise
twist comparison.
-/
@[stacks 07ZH] #check
  (AlgebraicGeometry.RelativeProjMap.comp_spec :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      (AlgebraicGeometry.RelativeProjMap.comp rφ rψ).domain =
          AlgebraicGeometry.RelativeProjMap.compDomain rφ rψ ∧
        (AlgebraicGeometry.RelativeProjMap.comp rφ rψ).map =
            AlgebraicGeometry.RelativeProjMap.compMap rφ rψ ∧
          ∀ n : ℤ,
            AlgebraicGeometry.RelativeProjMap.compTheta rφ rψ n =
              (AlgebraicGeometry.RelativeProjMap.comp rφ rψ).theta n)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) → Type (u + 1))

#check
  (AlgebraicGeometry.RelativeProjMap :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX)
      (Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra),
      Type u)

#check
  (AlgebraicGeometry.RelativeProjMap.overHom :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      (r : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ),
      Over.mk (r.domain.ι ≫ pY) ⟶ Over.mk pX)

#check
  (AlgebraicGeometry.RelativeProjMap.compDomain :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      Z.Opens)

#check
  (AlgebraicGeometry.RelativeProjMap.compMap :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      (AlgebraicGeometry.RelativeProjMap.compDomain rφ rψ).toScheme ⟶ X)

#check
  (AlgebraicGeometry.RelativeProjMap.compMiddleTwist :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ)
      (n : ℤ),
      (AlgebraicGeometry.RelativeProjMap.compDomain rφ rψ).toScheme.Modules)

#check
  (AlgebraicGeometry.RelativeProjMap.compPullbackTheta :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ)
      (n : ℤ),
      (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.RelativeProjMap.compMap rφ rψ)).obj (P𝒜.twist n) ⟶
        AlgebraicGeometry.RelativeProjMap.compMiddleTwist rφ rψ n)

#check
  (AlgebraicGeometry.RelativeProjMap.compThetaPsiOnCompDomain :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ)
      (n : ℤ),
      AlgebraicGeometry.RelativeProjMap.compMiddleTwist rφ rψ n ⟶
        (P𝒞.twist n).restrict
          (AlgebraicGeometry.RelativeProjMap.compDomain rφ rψ).ι)

#check
  (AlgebraicGeometry.RelativeProjMap.compTheta :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ)
      (n : ℤ),
      (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.RelativeProjMap.compMap rφ rψ)).obj (P𝒜.twist n) ⟶
        (P𝒞.twist n).restrict
          (AlgebraicGeometry.RelativeProjMap.compDomain rφ rψ).ι)

#check
  (AlgebraicGeometry.RelativeProjMap.compMap_over_base :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      AlgebraicGeometry.RelativeProjMap.compMap rφ rψ ≫ pX =
        (AlgebraicGeometry.RelativeProjMap.compDomain rφ rψ).ι ≫ pZ)

#check
  (AlgebraicGeometry.RelativeProjMap.comp :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      AlgebraicGeometry.RelativeProjMap P𝒜 P𝒞 (φ ≫ ψ))

#check
  (AlgebraicGeometry.RelativeProjMap.comp_domain :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      (AlgebraicGeometry.RelativeProjMap.comp rφ rψ).domain =
        AlgebraicGeometry.RelativeProjMap.compDomain rφ rψ)

#check
  (AlgebraicGeometry.RelativeProjMap.comp_map :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      (AlgebraicGeometry.RelativeProjMap.comp rφ rψ).map =
        AlgebraicGeometry.RelativeProjMap.compMap rφ rψ)

#check
  (AlgebraicGeometry.RelativeProjMap.comp_theta :
    ∀ {S X Y Z : AlgebraicGeometry.Scheme.{u}}
      {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
      {P𝒜 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pX}
      {Pℬ : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pY}
      {P𝒞 : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation pZ}
      {φ : P𝒜.algebra ⟶ Pℬ.algebra}
      {ψ : Pℬ.algebra ⟶ P𝒞.algebra}
      (rφ : AlgebraicGeometry.RelativeProjMap P𝒜 Pℬ φ)
      (rψ : AlgebraicGeometry.RelativeProjMap Pℬ P𝒞 ψ),
      ∀ n : ℤ,
        AlgebraicGeometry.RelativeProjMap.compTheta rφ rψ n =
          (AlgebraicGeometry.RelativeProjMap.comp rφ rψ).theta n)
