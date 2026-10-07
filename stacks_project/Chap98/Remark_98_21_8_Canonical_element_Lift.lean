module

public import stacks_project.Chap98.Lemma_98_21_2_Functor
public import stacks_project.Chap98.Lemma_98_21_2_Lifts
public import stacks_project.Chap98.Remark_98_21_9_Canonical_automorphism_Kaehler

/-!
# Canonical infinitesimal deformation along Kähler differentials

Pulling back a fibre object `x` over `Spec(A)` along the section
`a ↦ (a, d_{A/Λ}(a))` of `A[Ω_{A/Λ}]` produces the canonical lift
in `T_x(Ω_{A/Λ}) = Lift(x, A[Ω_{A/Λ}])`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {Λ A : CommRingCat.{u}} (v : Λ ⟶ A)
variable {σΛ : Spec Λ ⟶ S} {σA : Spec A ⟶ S} (hv : Spec.map v ≫ σΛ = σA)
variable (x : X.p.Fiber (Over.mk σA))

/-- The pullback of `x` along the section `a ↦ (a, d_{A/Λ}(a))`. -/
def canonicalDeformation :
    X.p.Fiber (Over.mk (specTrivSqZero σA (kaehlerObj v))) :=
  Chosen.reindexObj X.p (specOverCan v hv) x

/-- `canonicalDeformation` is selected reindexing of `x` along `specOverCan`. -/
theorem canonicalDeformation_eq :
    canonicalDeformation v hv x = Chosen.reindexObj X.p (specOverCan v hv) x :=
  sorry

/-- Identity of `x` lifts the composite of the coefficient projection with
`a ↦ (a, d_{A/Λ}(a))`. -/
theorem canonicalDeformation_id_isHomLift :
    X.p.IsHomLift
      (specOverHom (trivSqZeroHom A (kaehlerObj v)) (trivSqZeroHom_comp σA (kaehlerObj v)) ≫
        specOverCan v hv)
      (𝟙 (Fiber.fiberInclusion.obj x)) := sorry

/-- The canonical deformation of `x` to `Spec(A[Ω_{A/Λ}])`, as an object of the
lift category along `A[Ω_{A/Λ}] ⟶ A`. -/
def canonicalLift :
    liftCat x (trivSqZeroHom A (kaehlerObj v)) (trivSqZeroHom_comp σA (kaehlerObj v)) :=
  UnderLift.ofHom
    (specOverHom (trivSqZeroHom A (kaehlerObj v)) (trivSqZeroHom_comp σA (kaehlerObj v))) x
    (@Chosen.cartesianFactor _ _ _ _ X.p _
      (Over.mk σA) (Over.mk (specTrivSqZero σA (kaehlerObj v))) (Over.mk σA)
      (specOverCan v hv)
      (specOverHom (trivSqZeroHom A (kaehlerObj v)) (trivSqZeroHom_comp σA (kaehlerObj v)))
      x (Fiber.fiberInclusion.obj x) (𝟙 (Fiber.fiberInclusion.obj x))
      (canonicalDeformation_id_isHomLift v hv x))

/-- The canonical lift is a hom-lift of the coefficient projection
`A[Ω_{A/Λ}] ⟶ A`. -/
theorem canonicalLift_isHomLift :
    X.p.IsHomLift
      (specOverHom (trivSqZeroHom A (kaehlerObj v)) (trivSqZeroHom_comp σA (kaehlerObj v)))
      (canonicalLift v hv x).hom := sorry

variable [HasStrongRimSchlessinger X]

/-- The canonical element `x_can` of `T_x(Ω_{A/Λ})`, for an affine open
`Spec(Λ) ⊂ S`. -/
def canonicalElement (h_open : IsOpenImmersion σΛ) :
    (tangentFunctor x).obj (kaehlerObj v) :=
  have := h_open
  (tangentForget x (kaehlerObj v)).symm (lifts.mk (canonicalLift v hv x))

/-- The forgetful image of `canonicalElement` is the isomorphism class of
`canonicalLift`. -/
theorem canonicalElement_forget (h_open : IsOpenImmersion σΛ) :
    tangentForget x (kaehlerObj v) (canonicalElement v hv x h_open) =
      lifts.mk (canonicalLift v hv x) := sorry

/-- Evaluation of the canonical element along an `A`-linear map
`θ : Ω_{A/Λ} ⟶ M`, i.e. `T_x(θ)(x_can)`. -/
def evalCanonical (h_open : IsOpenImmersion σΛ) {M : ModuleCat.{u} A}
    (θ : kaehlerObj v ⟶ M) : (tangentFunctor x).obj M :=
  (tangentFunctor x).map θ (canonicalElement v hv x h_open)

/-- `evalCanonical θ` is `T_x` applied to `θ` at `canonicalElement`. -/
theorem evalCanonical_apply (h_open : IsOpenImmersion σΛ) {M : ModuleCat.{u} A}
    (θ : kaehlerObj v ⟶ M) :
    evalCanonical v hv x h_open θ =
      (tangentFunctor x).map θ (canonicalElement v hv x h_open) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
