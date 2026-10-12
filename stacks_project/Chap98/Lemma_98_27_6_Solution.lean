/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Situation_98_27_1_Contraction
public import stacks_project.Chap98.Lemma_98_27_4_Functor
public import stacks_project.Chap98.Lemma_98_25_2_Noetherian

/-!
# Solutions of Artin contractions

A solution for a contraction situation relative to an algebraic space `X` is a
proper morphism `f : X' ⟶ X`, a closed subset `T ⊂ |X|`, and an isomorphism
`a : X_/T ⟶ W` of formal algebraic spaces satisfying the inverse-image,
isomorphism-over-open, and completion-commutativity conditions. The restricted
functor of points of `X` on locally Noetherian schemes over `S` is the
comparison target of the contraction functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty Opposite
open TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor of points of an algebraic space `X` over `S`, restricted to
locally Noetherian schemes over `S`. On objects it sends `V` to
`Mor_S(V, X) = ofOver V ⟶ X`. -/
def homOnLocallyNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1) where
  obj V := ofOver V.unop.obj ⟶ X
  map φ := ofHom fun f ↦ ofOverMap φ.unop.hom ≫ f
  map_id := sorry
  map_comp := sorry

/-- The object map of `homOnLocallyNoetherian X` is `Mor_S(V, X)`. -/
theorem homOnLocallyNoetherian_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (V : (locallyNoetherian S).FullSubcategory) :
    (homOnLocallyNoetherian X).obj (op V) = (ofOver V.obj ⟶ X) :=
  sorry

/-- The morphism map of `homOnLocallyNoetherian X` is precomposition with
`ofOverMap`. -/
theorem homOnLocallyNoetherian_map {S : Scheme.{u}} (X : AlgebraicSpace S)
    {V1 V2 : (locallyNoetherian S).FullSubcategory} (φ : V2 ⟶ V1)
    (f : ofOver V1.obj ⟶ X) :
    (homOnLocallyNoetherian X).map φ.op f = ofOverMap φ.hom ≫ f :=
  sorry

/-- `homOnLocallyNoetherian X` is the restriction of the universe-raised functor
of points of `X` to locally Noetherian schemes over `S`. -/
def homOnLocallyNoetherian_isoUlift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    homOnLocallyNoetherian X ≅
      (restrictPresheaf S).obj
        (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  NatIso.ofComponents
    (fun V ↦
      { hom := ofHom fun f ↦ ULift.up (yonedaEquiv f)
        inv := ofHom fun x ↦ yonedaEquiv.symm x.down
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Components of `homOnLocallyNoetherian_isoUlift` are Yoneda evaluation into
`ULift`. -/
theorem homOnLocallyNoetherian_isoUlift_hom_app {S : Scheme.{u}}
    (X : AlgebraicSpace S) (V : (locallyNoetherian S).FullSubcategory)
    (f : ofOver V.obj ⟶ X) :
    ((homOnLocallyNoetherian_isoUlift X).hom.app (op V) f).down =
      yonedaEquiv f :=
  sorry

namespace completionAlong

/-- Transport of completions along an equality of closed subsets. -/
def congrClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T₁ T₂ : Closeds (Points X)} (h : T₁ = T₂) :
    completionAlong X T₁ ⟶ completionAlong X T₂ :=
  eqToHom (congrArg (completionAlong X) h)

/-- `congrClosed h` is identity transport of `completionAlong` along `h`. -/
theorem congrClosed_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T₁ T₂ : Closeds (Points X)} (h : T₁ = T₂) :
    congrClosed h = eqToHom (congrArg (completionAlong X) h) :=
  sorry

end completionAlong

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- A solution of a contraction situation relative to an algebraic space `X`
locally of finite type over `S`: a proper morphism `f : X' ⟶ X`, a closed
subset `T ⊂ |X|`, and an isomorphism `a : X_/T ⟶ W` such that `T'` is the
inverse image of `T`, `f` is an isomorphism over `X \ T`, and
`g = a ∘ f_/T`. -/
structure SolutionFor (σ : ContractionSituation S) (X : AlgebraicSpace S)
    [LocallyOfFiniteType (toBase X)] where
  /-- The morphism `f : X' ⟶ X`. -/
  f : σ.X' ⟶ X
  /-- `f` is proper. -/
  proper_f : Proper f
  /-- The closed subset `T ⊂ |X|`. -/
  T : Closeds (Points X)
  /-- The morphism `a : X_/T ⟶ W` of formal algebraic spaces. -/
  a : completionAlong X T ⟶ σ.W
  /-- `a` is an isomorphism. -/
  isIso_a : IsIso a
  /-- `T'` is the inverse image of `T` under `|f|`. -/
  inverseImage : σ.T' = T.preimage (Points.continuous_map f)
  /-- `f` identifies `U'` with the open complement `X \ T`. -/
  isoOverOpen : IsIsoOverOpen f (AlgebraicSpace.openComplementι X T)
  /-- `g = a ∘ f_/T` after transporting the completion of `X'` along
  `inverseImage`. -/
  commutes :
    completionAlong.congrClosed inverseImage ≫ completionAlong.map f T ≫ a = σ.g

namespace SolutionFor

variable {σ : ContractionSituation S} {X : AlgebraicSpace S}
  [LocallyOfFiniteType (toBase X)]

/-- Package a morphism `f : X' ⟶ X`, a closed subset `T ⊂ |X|`, and a morphism
`a : X_/T ⟶ W` as a solution. -/
def of (f : σ.X' ⟶ X) (T : Closeds (Points X))
    (a : completionAlong X T ⟶ σ.W) : SolutionFor σ X where
  f := f
  T := T
  a := a
  proper_f := sorry
  isIso_a := sorry
  inverseImage := sorry
  isoOverOpen := sorry
  commutes := sorry

/-- A solution records a proper morphism, an isomorphism of completions, the
inverse-image relation, an isomorphism over the open complement, and
commutativity with `g`. -/
theorem spec (sol : SolutionFor σ X) :
    Proper sol.f ∧ IsIso sol.a ∧
      σ.T' = sol.T.preimage (Points.continuous_map sol.f) ∧
      IsIsoOverOpen sol.f (AlgebraicSpace.openComplementι X sol.T) ∧
      completionAlong.congrClosed sol.inverseImage ≫
          completionAlong.map sol.f sol.T ≫ sol.a =
        σ.g :=
  sorry

/-- The induced morphism `f_/T : X'_/T' ⟶ X_/T` of completions. -/
def mapCompletion (sol : SolutionFor σ X) :
    σ.completion ⟶ completionAlong X sol.T :=
  completionAlong.congrClosed sol.inverseImage ≫
    completionAlong.map sol.f sol.T

/-- Postcomposing `mapCompletion` with `a` recovers `g`. -/
theorem mapCompletion_comp (sol : SolutionFor σ X) :
    sol.mapCompletion ≫ sol.a = σ.g :=
  sorry

end SolutionFor

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
