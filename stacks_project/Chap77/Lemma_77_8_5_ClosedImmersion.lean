module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap68.Lemma_68_17_2
public import stacks_project.Chap77.Definition_77_3_1_Purity
public import stacks_project.Chap77.Lemma_77_8_5_ZeroFunctor
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Algebraic-space structure on the vanishing functor

Under finite presentation of the morphism and of `𝒢`, together with relative flatness
and purity of `𝒢`, the `(Sch/S)` functor `F_zero` is an algebraic space, and the
structure map `F_zero ⟶ B` is a closed immersion. If `ℱ` is of finite type, that
closed immersion is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

namespace zeroOverSFunctor

/-- If `f` and `𝒢` are of finite presentation and `𝒢` is flat over `B` and pure relative
to `B`, then the `(Sch/S)` vanishing functor is an algebraic space. -/
theorem isAlgebraicSpace [FinitePresentation f] [𝒢.IsFinitePresentation]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (hG_pure : 𝒢.IsPureOver f)
    (u : ℱ ⟶ 𝒢) :
    IsAlgebraicSpace (zeroOverSFunctor f u) :=
  sorry

/-- If `f` and `𝒢` are of finite presentation and `𝒢` is flat over `B` and pure relative
to `B`, then the structure morphism `F_zero ⟶ B` is a closed immersion. -/
theorem isClosedImmersion_toB [FinitePresentation f] [𝒢.IsFinitePresentation]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (hG_pure : 𝒢.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  sorry

/-- If in addition `ℱ` is of finite type, then the structure morphism `F_zero ⟶ B` is
of finite presentation. -/
theorem finitePresentation_toB [FinitePresentation f] [𝒢.IsFinitePresentation]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (hG_pure : 𝒢.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  sorry

end zeroOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
