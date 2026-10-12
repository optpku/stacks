/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.KoszulAt :
  {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → X → Prop)

#check (AlgebraicGeometry.Scheme.Hom.koszulAt_iff :
  {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) → (x : X) →
    (AlgebraicGeometry.Scheme.Hom.KoszulAt f x ↔
      AlgebraicGeometry.Scheme.Hom.FiniteTypeAt f x ∧
        ∃ U : X.Opens, x ∈ U ∧
          ∃ (P : AlgebraicGeometry.Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ S),
            AlgebraicGeometry.IsKoszulRegularImmersion i ∧
              AlgebraicGeometry.Smooth π ∧ i ≫ π = U.ι ≫ f))

#check (AlgebraicGeometry.Scheme.Hom.KoszulAt.finiteTypeAt :
  {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) → {x : X} →
    AlgebraicGeometry.Scheme.Hom.KoszulAt f x →
      AlgebraicGeometry.Scheme.Hom.FiniteTypeAt f x)

#check (AlgebraicGeometry.Scheme.Hom.KoszulAt.exists_factorization :
  {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) → {x : X} →
    AlgebraicGeometry.Scheme.Hom.KoszulAt f x →
      ∃ U : X.Opens, x ∈ U ∧
        ∃ (P : AlgebraicGeometry.Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ S),
          AlgebraicGeometry.IsKoszulRegularImmersion i ∧
            AlgebraicGeometry.Smooth π ∧ i ≫ π = U.ι ≫ f)

#check (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_iff_forall_koszulAt :
  {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) →
    (AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f ↔
      ∀ x : X, AlgebraicGeometry.Scheme.Hom.KoszulAt f x))

#check (AlgebraicGeometry.LocallyOfType.koszulAt :
  {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) →
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f →
      (x : X) → AlgebraicGeometry.Scheme.Hom.KoszulAt f x)
