module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Deformation.Presentation

/-! # Compatible cogroupoid presentations of predeformation functors -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicStack (FieldValuedPoint)
open FiberedCategoryOver.Groupoids
open CompleteLocalAlgCat
open GroupoidInFunctors
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
  [AlgebraicStack X]
  [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
  (x0 : FieldValuedPoint X)
  [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
  {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
  [Module.Finite Λ x0.K]
  (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
  [IsOpenImmersion openImmersion]
  (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
      x0.structureHom)

/-- A coyoneda cogroupoid on `(ξ.base, B, s, t, c)` presents the predeformation
functor of `ξ` when its restriction to Artinian local algebras is isomorphic to
`ofFormalObject ξ` by an isomorphism that is the identity on objects. -/
def IsPredeformationCogroupoid
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B) (c : B ⟶ pushout s t) : Prop :=
  ∃ (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
    (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
    (laws : CoyonedaGroupoidLaws s t c idMap invMap)
    (ε : GroupoidInFunctors.Iso
      (restrictInclusion (ofCoyoneda s t c idMap invMap laws))
      (ofFormalObject ξ)),
    ε.hom.obj = 𝟙 _

/-- A compatible predeformation cogroupoid is equivalently a choice of identity
and inverse maps satisfying the cogroupoid laws, together with an isomorphism
of its restriction to `ofFormalObject ξ` that is the identity on objects. -/
theorem isPredeformationCogroupoid_iff
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B) (c : B ⟶ pushout s t) :
    IsPredeformationCogroupoid x0 openImmersion h_factor ξ B s t c ↔
      ∃ (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
        (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
        (laws : CoyonedaGroupoidLaws s t c idMap invMap)
        (ε : GroupoidInFunctors.Iso
          (restrictInclusion (ofCoyoneda s t c idMap invMap laws))
          (ofFormalObject ξ)),
        ε.hom.obj = 𝟙 _ := by
  rfl

end AlgebraicGeometry.GroupoidsOver.Predeformation
