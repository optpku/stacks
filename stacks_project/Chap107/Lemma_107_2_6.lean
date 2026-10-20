module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Versality
import StacksCheckRecall

/-!
# Versality at a finite type point versus smoothness of an open restriction

In Situation 107.2.1, versality of `x` at a finite type point `u0` is equivalent
to smoothness of `hat x`, versality of the associated formal object, and
smoothness of `x` after restriction to some open neighbourhood of `u0`. In that
case the completed stalk is a versal ring at the induced field-valued point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

open GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.2.6 (1): In Situation 107.2.1 let `x : U ⟶ X` be a morphism where
`U` is a scheme locally of finite type over `S`. Let `u0 ∈ U` be a finite type
point. Set `k = κ(u0)` and denote `x0 : Spec(k) ⟶ X` the induced map. The
following are equivalent: `x` is versal at `u0`; `hat x : F_{U, k, u0} ⟶
F_{X, k, x0}` is smooth; the formal object associated to `x` restricted to
`Spec(O_{U, u0}^∧)` is versal; and there is an open neighbourhood `U' ⊆ U` of
`u0` such that `x|_{U'} : U' ⟶ X` is smooth. -/
@[stacks 0DQZ]
#check (AlgebraicGeometry.AlgebraicStack.isVersalAt_tfae :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    List.TFAE
      [IsVersalAt hU x hx u0,
        (∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
          [Algebra Λ (residueFieldType u0)]
          [Module.Finite Λ (residueFieldType u0)]
          (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
          [IsOpenImmersion openImmersion]
          (h_factor :
            Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
                openImmersion =
              fromResidueField u0 ≫ hU),
          BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor)),
        GroupoidsOver.FormalObject.IsVersal (associatedFormalObject hU x hx u0),
        ∃ U' : U.Opens, u0 ∈ U' ∧
          Groupoids.Hom.Smooth (restrictToOpen hU x hx U')])

#check (AlgebraicGeometry.AlgebraicStack.isVersalAt_iff_exists_isSmooth_restrict :
  ∀ {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    IsVersalAt hU x hx u0 ↔
      ∃ U' : U.Opens, u0 ∈ U' ∧
        Groupoids.Hom.Smooth (restrictToOpen hU x hx U'))

#check (AlgebraicGeometry.AlgebraicStack.instIsVersalRing_completionSAlgebra :
  ∀ {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0],
    IsVersalRing (FieldValuedPoint.induced hU x hx u0)
      (completionSAlgebra hU u0))

end AlgebraicGeometry.AlgebraicStack
