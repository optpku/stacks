module

public import stacks_project.Chap50.Proposition_50_24_5_Duality

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed RingedSite.Hom TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

-- Local instance justification (defeq pin): align the imported duality API with the coefficient-site derived-category presentation fixed by `derivedComplex`.
attribute [local instance] moduleCat_hasDerivedCategory

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
variable [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
variable [Scheme.Hom.RelativeDimension f n]
variable [MonoidalCategory (ModuleDerived.{u} (PoincareDuality.sourceSite f))]
variable [Functor.LaxMonoidal
  (moduleLocalization.{u} (PoincareDuality.sourceSite f))]
variable [MonoidalCategory (ModuleDerived.{u} (PoincareDuality.targetSite S))]
variable [(PoincareDuality.cupHom f).modulePushforward.IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u} (PoincareDuality.cupHom f))
  (ModuleQis.{u} (PoincareDuality.sourceSite f))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{u} (PoincareDuality.cupHom f))
  (ModuleQis.{u} (PoincareDuality.targetSite S))]
variable [DerivedAdjunction.HasPair.{u} (PoincareDuality.cupHom f)]
variable [(modulePullbackDerived.{u} (PoincareDuality.cupHom f)).OplaxMonoidal]
variable [((tensoringLeft (ModuleDerived.{u} (PoincareDuality.targetSite S))).obj
  (PoincareDuality.pushforward f)).CommShift ℤ]
variable [MonoidalClosed (ModuleDerived.{u} (PoincareDuality.targetSite S))]
variable [BraidedCategory (ModuleDerived.{u} (PoincareDuality.targetSite S))]

/-- Proposition 50.24.5 (1): for a proper smooth morphism with nonempty fibres of relative
dimension `n`, there is a trace inducing an `𝒪_S`-module map on
`R^(2 * n)f_*Ωᵈᴿ[X/S]` whose cup-trace pairing on `Rf_*Ωᵈᴿ[X/S]` is perfect. -/
@[stacks 0G8K]
theorem existsRelativeDeRhamPoincareTrace
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) :
    ∃ t : PoincareDuality.topCohomology f n ⟶ PoincareDuality.structureModule S,
      ∃ τ : (PoincareDuality.pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
          𝟙_ (ModuleDerived.{u} (PoincareDuality.targetSite S)),
        PoincareDuality.topTrace f n τ = t ∧ PoincareDuality.IsPerfect f n τ := sorry

/-- Proposition 50.24.5 (2): the induced maps on `R^(2 * n)f_*Ωᵈᴿ[X/S]` of any two
perfect traces differ by precomposition with multiplication by a unit of `Γ(X, ⊤)`. -/
@[stacks 0G8K]
theorem relativeDeRhamPoincareTrace_unique
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s))
    (t t' : PoincareDuality.topCohomology f n ⟶ PoincareDuality.structureModule S)
    (τ τ' : (PoincareDuality.pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (PoincareDuality.targetSite S)))
    (ht : PoincareDuality.topTrace f n τ = t)
    (ht' : PoincareDuality.topTrace f n τ' = t')
    (hτ : PoincareDuality.IsPerfect f n τ)
    (hτ' : PoincareDuality.IsPerfect f n τ') :
    ∃ a : Γ(X, ⊤)ˣ,
      t' = PoincareDuality.unitAction f n h_nonempty a ≫ t := sorry

end AlgebraicGeometry.Scheme.DeRham
