module

public import stacks_project.Chap98.Definition_98_9_1_AlgebraHom

/-!
# Morphisms of formal objects of a category fibred in groupoids

A morphism of formal objects is a natural family of morphisms in the total
category, together with the induced morphism of complete local `S`-algebras
over which the family lies.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S}

/-- A morphism of formal objects is a natural family `a_n : ξ_n ⟶ η_n` lying
over the truncated spectra of a morphism of complete local `S`-algebras. -/
structure Hom (ξ η : FormalObject X) where
  /-- Stagewise morphisms `a_n : ξ_n ⟶ η_n` of the forward systems. -/
  app : ∀ n, ξ.objects n ⟶ η.objects n
  /-- Induced morphism of complete local `S`-algebras, giving `a0`. -/
  base : CompleteLocalSAlgebra.Hom ξ.base η.base
  /-- Each `a_n` lies over the truncated map `Spec(R ⧸ m^{n+1}) ⟶ Spec(T ⧸ m^{n+1})`. -/
  over : ∀ n, X.p.IsHomLift (base.stageMap n) (app n)
  /-- The family `(a_n)` intertwines successor transitions. -/
  naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n

/-- Package a natural family over a morphism of complete local `S`-algebras as
a morphism of formal objects. -/
def Hom.of {ξ η : FormalObject X} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (base : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, X.p.IsHomLift (base.stageMap n) (app n))
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) :
    Hom ξ η where
  app := app
  base := base
  over := over
  naturality := naturality

/-- Identity morphism of a formal object. -/
def Hom.id (ξ : FormalObject X) : Hom ξ ξ where
  app := fun n ↦ 𝟙 (ξ.objects n)
  base := CompleteLocalSAlgebra.Hom.id ξ.base
  over := sorry
  naturality := sorry

/-- Composition of morphisms of formal objects, covariant on stage maps and on
the induced spectra. -/
def Hom.comp {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ where
  app := fun n ↦ a.app n ≫ b.app n
  base := CompleteLocalSAlgebra.Hom.comp a.base b.base
  over := sorry
  naturality := sorry

/-- The identity morphism has identity stage maps. -/
theorem Hom.id_app (ξ : FormalObject X) (n : ℕ) :
    (Hom.id ξ).app n = 𝟙 (ξ.objects n) := sorry

/-- The identity morphism has identity base map. -/
theorem Hom.id_base (ξ : FormalObject X) :
    (Hom.id ξ).base = CompleteLocalSAlgebra.Hom.id ξ.base := sorry

/-- Composition of morphisms of formal objects composes stage maps. -/
theorem Hom.comp_app {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ)
    (n : ℕ) : (Hom.comp a b).app n = a.app n ≫ b.app n := sorry

/-- Composition of morphisms of formal objects composes base maps. -/
theorem Hom.comp_base {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) :
    (Hom.comp a b).base = CompleteLocalSAlgebra.Hom.comp a.base b.base :=
  sorry

/-- A morphism of formal objects lies over its truncated base maps and commutes
with successor transitions. -/
theorem Hom.spec {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    X.p.IsHomLift (a.base.stageMap n) (a.app n) ∧
      ξ.step n ≫ a.app (n + 1) = a.app n ≫ η.step n := sorry

/-- The induced scheme morphism `a0 : Spec(R) ⟶ Spec(T)`. -/
def Hom.overMorphism {ξ η : FormalObject X} (a : Hom ξ η) :
    Spec (CommRingCat.of ξ.base.carrier) ⟶ Spec (CommRingCat.of η.base.carrier) :=
  a.base.toSpec

/-- `overMorphism` is the spectrum of the stored base homomorphism. -/
theorem Hom.overMorphism_eq {ξ η : FormalObject X} (a : Hom ξ η) :
    a.overMorphism = a.base.toSpec := sorry

/-- A morphism of formal objects lies over its induced morphism `a0` of spectra
over `S`. -/
theorem Hom.liesOver {ξ η : FormalObject X} (a : Hom ξ η) :
    a.overMorphism ≫ η.base.toS = ξ.base.toS := sorry

end AlgebraicGeometry.GroupoidsOver.FormalObject
