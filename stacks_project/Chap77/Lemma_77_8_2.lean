module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver
public import stacks_project.Chap77.«77_7_1_1_BaseChange»

/-!
# Making a map of quasi-coherent modules vanish on a closed subscheme

Over an affine base, vanishing of a quasi-coherent map after quasi-compact base change
is witnessed by a closed subscheme of the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 77.8.2 (1): In Situation 77.8.1, with `S` affine, `X` an algebraic space over
`S`, and `u : ℱ ⟶ 𝒢` a map of quasi-coherent modules with `𝒢` flat over `S`, let
`g : T ⟶ S` be a quasi-compact morphism of schemes such that the base change `u_T` is
zero, that is `baseChangeMap (toBase X) (ofOverHomMk g (Category.comp_id g)) u = 0`.
Then there exists a closed subscheme `Z ⊂ S`, packaged as `Z : Over S` with
`AlgebraicGeometry.IsClosedImmersion Z.hom`, such that `T ⟶ S` factors through `Z` as an
`Over`-morphism `Over.mk g ⟶ Z`, and the base change `u_Z` is zero. -/
@[stacks 083K]
theorem exists_closedImmersion_of_baseChangeMap_eq_zero
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 (toBase X) x) (u : ℱ ⟶ 𝒢)
    {T : Scheme.{u}} (g : T ⟶ S) [QuasiCompact g]
    (hu : baseChangeMap (toBase X) (ofOverHomMk g (Category.comp_id g)) u = 0) :
    ∃ Z : Over S, AlgebraicGeometry.IsClosedImmersion Z.hom ∧
      Nonempty (Over.mk g ⟶ Z) ∧
        baseChangeMap (toBase X) (ofOverHomMk Z.hom (Category.comp_id Z.hom)) u = 0 :=
  sorry

/-- Lemma 77.8.2 (2): In Situation 77.8.1, if moreover `ℱ` is of finite type and the
scheme-theoretic support of `ℱ` is quasi-compact, then the closed subscheme `Z ⊂ S`
through which `T ⟶ S` factors with `u_Z = 0` may be taken of finite presentation. -/
@[stacks 083K]
theorem exists_closedImmersion_of_baseChangeMap_eq_zero_of_finitePresentation
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [ℱ.IsFiniteType]
    [IsQuasiCompact (schemeTheoreticSupport ℱ).X]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 (toBase X) x) (u : ℱ ⟶ 𝒢)
    {T : Scheme.{u}} (g : T ⟶ S) [QuasiCompact g]
    (hu : baseChangeMap (toBase X) (ofOverHomMk g (Category.comp_id g)) u = 0) :
    ∃ Z : Over S,
      (AlgebraicGeometry.IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom) ∧
        Nonempty (Over.mk g ⟶ Z) ∧
          baseChangeMap (toBase X) (ofOverHomMk Z.hom (Category.comp_id Z.hom)) u = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
