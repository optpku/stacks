module

public import stacks_project.Chap63.Lemma_63_4_11_Comparison
public import stacks_project.Chap63.Lemma_63_4_11_Pullback

/-!
# Mixed composition of locally quasi-finite and compact-support lower shriek

Lemma 63.4.11: for composable scheme morphisms `f' : X ⟶ Y'` and `g : Y' ⟶ Y`
with `f'` and `f = f' ≫ g` locally quasi-finite and `g` separated and locally
of finite type, there is a canonical functor isomorphism `f_! ≅ g_! ∘ f'_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y' Y : Scheme.{u}} (f' : X ⟶ Y') (g : Y' ⟶ Y)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [LocallyQuasiFinite (f' ≫ g)] [LocallyOfFiniteType (f' ≫ g)]
variable [IsSeparated g] [LocallyOfFiniteType g]

/-- Lemma 63.4.11 (1): Let `f' : X ⟶ Y'` and `g : Y' ⟶ Y` be composable morphisms
of schemes with `f'` and `f = f' ≫ g` locally quasi-finite and `g` separated
and locally of finite type. Then there is a canonical isomorphism of functors
`f_! ≅ g_! ∘ f'_!`, i.e.
`lowerShriek (f' ≫ g) ≅ lowerShriek f' ⋙ etaleLowerShriek g`,
with forward map the constructed comparison `c'`. -/
@[stacks 0F79]
def lowerShriekCompIso :
    lowerShriek (f' ≫ g) ≅ lowerShriek f' ⋙ etaleLowerShriek g :=
  asIso (lowerShriekComp f' g)

/-- The objectwise identification `(f' ≫ g)_! F ≅ g_! (f'_! F)` at an abelian
étale sheaf `F`. -/
def lowerShriekCompIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f' ≫ g)).obj F ≅
      (etaleLowerShriek g).obj ((lowerShriek f').obj F) :=
  (lowerShriekCompIso f' g).app F

/-- The forward map of `lowerShriekCompIso` is the constructed mixed
composition comparison `c'`. -/
theorem lowerShriekCompIso_hom :
    (lowerShriekCompIso f' g).hom = lowerShriekComp f' g :=
  sorry

section openImmersion

variable {X₁ Y₁' : Scheme.{u}} (a : X₁ ⟶ X) (f₁' : X₁ ⟶ Y₁') (j' : Y₁' ⟶ Y')
variable (h_cart : IsPullback a f₁' f' j')
variable [IsOpenImmersion a] [IsOpenImmersion j']
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ j' ≫ g)] [LocallyOfFiniteType (f₁' ≫ j' ≫ g)]
variable [LocallyQuasiFinite (a ≫ f' ≫ g)] [LocallyOfFiniteType (a ≫ f' ≫ g)]
variable [IsSeparated (j' ≫ g)] [LocallyOfFiniteType (j' ≫ g)]

/-- Lemma 63.4.11 (2): the mixed composition isomorphism is compatible with
covariance along open immersions as in Remarks 63.3.5 and 63.4.6. -/
@[stacks 0F79]
theorem lowerShriekCompIso_openImmersion :
    lowerShriekCompIso_openImmersion_inner f' g a f₁' j' h_cart =
      lowerShriekCompIso_openImmersion_outer f' g a :=
  sorry

end openImmersion

section baseChange

variable {X₁ Y₁' Y₁ : Scheme.{u}}
variable (f₁' : X₁ ⟶ Y₁') (g₁ : Y₁' ⟶ Y₁) (b : Y₁ ⟶ Y)
variable (b' : Y₁' ⟶ Y') (a : X₁ ⟶ X)
variable (h_upper : IsPullback a f₁' f' b') (h_lower : IsPullback b' g₁ g b)
variable [LocallyQuasiFinite f₁'] [LocallyOfFiniteType f₁']
variable [LocallyQuasiFinite (f₁' ≫ g₁)] [LocallyOfFiniteType (f₁' ≫ g₁)]
variable [IsSeparated g₁] [LocallyOfFiniteType g₁]

/-- Lemma 63.4.11 (3): the mixed composition isomorphism is compatible with
the base-change isomorphisms of Lemmas 63.4.10 and 63.3.12. -/
@[stacks 0F79]
theorem lowerShriekCompIso_baseChange :
    lowerShriekCompIso_baseChange_inner f' g f₁' g₁ b b' a h_upper h_lower =
      lowerShriekCompIso_baseChange_outer f' g f₁' g₁ b b' a h_upper h_lower :=
  sorry

end baseChange

section separated

variable [IsSeparated f']

/-- Lemma 63.4.11 (4): if `f'` is separated, the mixed composition isomorphism
agrees with the isomorphism of Lemma 63.3.13 via the identifications of
Lemma 63.4.1. -/
@[stacks 0F79]
theorem lowerShriekCompIso_separated :
    lowerShriekCompIso_separated_left f' g =
      lowerShriekCompIso_separated_right f' g :=
  sorry

end separated

end AlgebraicGeometry.Scheme.Etale

end
