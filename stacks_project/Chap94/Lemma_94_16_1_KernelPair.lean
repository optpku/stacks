module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Symmetry.Swap
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Lemma_94_9_8
public import stacks_project.Chap94.Lemma_94_10_11

/-!
# Kernel pair of a 1-morphism into an algebraic stack

The self 2-fibre product `R = U ×_{f, X, f} U` of a 1-morphism from a space-representable
algebraic stack, together with the canonical triple equivalence and the outer projection
`pr₀₂`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X U : GroupoidsOver S}

/-- The kernel pair of a 1-morphism `f : U ⟶ X` of categories fibred in groupoids over
`(Sch/S)_fppf`, realized as the chosen self 2-fibre product `TwoFibreProduct.apex f f`. -/
abbrev kernelPair (f : U ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f

/-- `kernelPair f` is the chosen self 2-fibre product of `f`. -/
theorem kernelPair_eq (f : U ⟶ X) :
    kernelPair f = TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f :=
  sorry

/-- The projection `pr₀ : R ⟶ U` of the kernel pair, corresponding to the first factor. -/
abbrev pr0 (f : U ⟶ X) : kernelPair f ⟶ U :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f

/-- The projection `pr₁ : R ⟶ U` of the kernel pair, corresponding to the second factor. -/
abbrev pr1 (f : U ⟶ X) : kernelPair f ⟶ U :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f

/-- `pr0 f` is the first projection of the self 2-fibre product of `f`. -/
theorem pr0_eq (f : U ⟶ X) :
    pr0 f = TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f :=
  sorry

/-- `pr1 f` is the second projection of the self 2-fibre product of `f`. -/
theorem pr1_eq (f : U ⟶ X) :
    pr1 f = TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f :=
  sorry

/-- The kernel pair of a 1-morphism from a space-representable algebraic stack into an
algebraic stack is representable by an algebraic space. -/
theorem kernelPair_isRepresentableByAlgebraicSpace (f : U ⟶ X) [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U) :
    IsRepresentableByAlgebraicSpace (kernelPair f) :=
  sorry

/-- The left-associated triple 2-fibre product
`(U ×_{f, X, f} U) ×_{f, X, f} U`. -/
abbrev tripleProduct (f : U ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f ≫ f) f

/-- The fibre product of the kernel pair with itself over `U` along `(pr₁, pr₀)`. -/
abbrev kernelPairPair (f : U ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (pr1 f) (pr0 f)

/-- `tripleProduct f` is the left-associated iterated self 2-fibre product of `f`. -/
theorem tripleProduct_eq (f : U ⟶ X) :
    tripleProduct f =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f ≫ f) f :=
  sorry

/-- `kernelPairPair f` is the 2-fibre product of `pr1 f` against `pr0 f`. -/
theorem kernelPairPair_eq (f : U ⟶ X) :
    kernelPairPair f =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (pr1 f) (pr0 f) :=
  sorry

/-- The identity cone on `f` with apex `U`, used to produce the identity arrow of the
kernel pair. -/
def identityCone (f : U ⟶ X) : PseudoPullbackCone f f where
  pt := U
  fst := 𝟙 U
  snd := 𝟙 U
  iso := Iso.refl (𝟙 U ≫ f)

/-- The identity 1-morphism `U ⟶ R` induced by the identity 2-cell of `f`. -/
def identityHom (f : U ⟶ X) : U ⟶ kernelPair f :=
  PseudoPullbackCone.lift (identityCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- `identityHom f` is the universal lift of the identity cone on `f`. -/
theorem identityHom_eq (f : U ⟶ X) :
    identityHom f =
      PseudoPullbackCone.lift (identityCone f)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f) :=
  sorry

/-- The first two factors of the left-associated triple product, as a 1-morphism to the
kernel pair. -/
abbrev triplePr01 (f : U ⟶ X) : tripleProduct f ⟶ kernelPair f :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f ≫ f) f

/-- The third factor of the left-associated triple product. -/
abbrev triplePr2 (f : U ⟶ X) : tripleProduct f ⟶ U :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u}
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f ≫ f) f

/-- The cone on `f, f` whose apex is the triple product and whose object is the last two
factors `(b, c, β)`. -/
def secondFactorCone (f : U ⟶ X) : PseudoPullbackCone f f where
  pt := tripleProduct f
  fst := triplePr01 f ≫ pr1 f
  snd := triplePr2 f
  iso :=
    α_ (triplePr01 f) (pr1 f) f ≪≫
      TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f ≫ f) f

/-- The 1-morphism from the triple product to the kernel pair selecting the last two
factors. -/
def secondFactor (f : U ⟶ X) : tripleProduct f ⟶ kernelPair f :=
  PseudoPullbackCone.lift (secondFactorCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- `secondFactor f` is the universal lift of `secondFactorCone f`. -/
theorem secondFactor_eq (f : U ⟶ X) :
    secondFactor f =
      PseudoPullbackCone.lift (secondFactorCone f)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f) :=
  sorry

/-- The cone on `(pr₁, pr₀)` with apex the left-associated triple product. On fibre
categories it sends `((a, b, α), c, β)` to `((a, b, α), (b, c, β))`. -/
def tripleCone (f : U ⟶ X) : PseudoPullbackCone (pr1 f) (pr0 f) where
  pt := tripleProduct f
  fst := triplePr01 f
  snd := secondFactor f
  iso :=
    (PseudoPullbackCone.lift.fstIso (secondFactorCone f)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)).symm

/-- The left-associated triple product is a 2-fibre product of `pr1 f` against `pr0 f`. -/
instance tripleCone.isBilimit (f : U ⟶ X) : (tripleCone f).IsBilimit :=
  sorry

/-- The canonical equivalence
`U ×_{f, X, f} U ×_{f, X, f} U ≌ R ×_{pr₁, U, pr₀} R`
obtained by comparing the two bilimits of the cospan `(pr₁, pr₀)`. -/
def tripleEquiv (f : U ⟶ X) : tripleProduct f ≌ kernelPairPair f :=
  PseudoPullbackCone.apexEquivalence (tripleCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (pr1 f) (pr0 f))

/-- The forward 1-morphism of `tripleEquiv f` is the universal lift of `tripleCone f`. -/
theorem tripleEquiv_hom (f : U ⟶ X) :
    (tripleEquiv f).hom =
      PseudoPullbackCone.lift (tripleCone f)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (pr1 f) (pr0 f)) :=
  sorry

/-- The inverse 1-morphism of `tripleEquiv f` is the reverse universal lift. -/
theorem tripleEquiv_inv (f : U ⟶ X) :
    (tripleEquiv f).inv =
      PseudoPullbackCone.lift
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (pr1 f) (pr0 f)) (tripleCone f) :=
  sorry

/-- The first projection of `kernelPairPair f` to the kernel pair. -/
abbrev pairPr0 (f : U ⟶ X) : kernelPairPair f ⟶ kernelPair f :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} (pr1 f) (pr0 f)

/-- The second projection of `kernelPairPair f` to the kernel pair. -/
abbrev pairPr1 (f : U ⟶ X) : kernelPairPair f ⟶ kernelPair f :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} (pr1 f) (pr0 f)

/-- The cone on `f, f` whose apex is `R ×_{pr₁, U, pr₀} R` and whose object is the outer
pair `(a, c, β ∘ α)`. -/
def pr02Cone (f : U ⟶ X) : PseudoPullbackCone f f where
  pt := kernelPairPair f
  fst := pairPr0 f ≫ pr0 f
  snd := pairPr1 f ≫ pr1 f
  iso :=
    α_ (pairPr0 f) (pr0 f) f ≪≫
      whiskerLeftIso (pairPr0 f)
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f f) ≪≫
      (α_ (pairPr0 f) (pr1 f) f).symm ≪≫
      whiskerRightIso
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (pr1 f) (pr0 f)) f ≪≫
      α_ (pairPr1 f) (pr0 f) f ≪≫
      whiskerLeftIso (pairPr1 f)
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f f) ≪≫
      (α_ (pairPr1 f) (pr1 f) f).symm

/-- The outer projection `pr₀₂ : R ×_{pr₁, U, pr₀} R ⟶ R` induced by the 2-fibre product
of `f` with itself. On fibre categories it sends `((a, b, α), (b, c, β))` to
`(a, c, β ∘ α)`. -/
def pr02 (f : U ⟶ X) : kernelPairPair f ⟶ kernelPair f :=
  PseudoPullbackCone.lift (pr02Cone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- `pr02 f` is the universal lift of the outer-pair cone on `f`. -/
theorem pr02_eq (f : U ⟶ X) :
    pr02 f =
      PseudoPullbackCone.lift (pr02Cone f)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f) :=
  sorry

/-- The first projection of `pr02 f` recovers the outer source `a`. -/
def pr02_fstIso (f : U ⟶ X) :
    pr02 f ≫ pr0 f ≅ pairPr0 f ≫ pr0 f :=
  PseudoPullbackCone.lift.fstIso (pr02Cone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- The second projection of `pr02 f` recovers the outer target `c`. -/
def pr02_sndIso (f : U ⟶ X) :
    pr02 f ≫ pr1 f ≅ pairPr1 f ≫ pr1 f :=
  PseudoPullbackCone.lift.sndIso (pr02Cone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- The identity 1-morphism of the kernel pair projects to the identity on `U`
along `pr0`. -/
def identityHom_fstIso (f : U ⟶ X) :
    identityHom f ≫ pr0 f ≅ 𝟙 U :=
  PseudoPullbackCone.lift.fstIso (identityCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- The identity 1-morphism of the kernel pair projects to the identity on `U`
along `pr1`. -/
def identityHom_sndIso (f : U ⟶ X) :
    identityHom f ≫ pr1 f ≅ 𝟙 U :=
  PseudoPullbackCone.lift.sndIso (identityCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

end AlgebraicGeometry.AlgebraicStack
