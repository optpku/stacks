/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import stacks_project.Chap61.Definition_61_29_4_Completion

/-!
# Termwise completed-constant models in `D(J, Λ)`

A derived sheaf of `Λ`-modules has a termwise completed-constant model when it
is isomorphic to a bounded cochain complex whose terms are completed constant
sheaves of finite projective `Λ^∧`-modules, with arbitrary sheaf differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.ProEt

namespace Derived

variable {Λ : Type w} [CommRing Λ]
variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (I : Ideal Λ)
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- `DerivedCategory.Q` is typed using `Abelian.toPreadditive`.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

/-- A derived sheaf of `Λ`-modules has a termwise completed-constant model relative
to `I` when it is isomorphic in the derived category to a bounded cochain complex
whose terms are completed constant sheaves of finite projective `Λ^∧`-modules.
Differentials are arbitrary sheaf maps, not necessarily induced by module maps. -/
def HasTermwiseCompletedConstantModel
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) : Prop :=
  ∃ P : CochainComplex.Bounded (Sheaf J (ModuleCat.{w} Λ)),
    ∃ _ : DerivedCategory.Q.obj P.obj ≅ K,
      ∀ n : ℤ,
        ∃ M : ModuleCat.{w} (AdicCompletion I Λ),
          Module.Finite (AdicCompletion I Λ) M ∧
            Module.Projective (AdicCompletion I Λ) M ∧
              Nonempty (P.obj.X n ≅ constantAdicCompletionSheaf J I M)

/-- Unfolding `HasTermwiseCompletedConstantModel` recovers a bounded termwise
completed-constant witness. -/
theorem hasTermwiseCompletedConstantModel_iff
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    HasTermwiseCompletedConstantModel J I K ↔
      ∃ P : CochainComplex.Bounded (Sheaf J (ModuleCat.{w} Λ)),
        ∃ _ : DerivedCategory.Q.obj P.obj ≅ K,
          ∀ n : ℤ,
            ∃ M : ModuleCat.{w} (AdicCompletion I Λ),
              Module.Finite (AdicCompletion I Λ) M ∧
                Module.Projective (AdicCompletion I Λ) M ∧
                  Nonempty (P.obj.X n ≅ constantAdicCompletionSheaf J I M) :=
  sorry

/-- Termwise completed-constant models transport along derived isomorphisms. -/
theorem hasTermwiseCompletedConstantModel_of_iso
    {K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    (e : K ≅ L) (h : HasTermwiseCompletedConstantModel J I K) :
    HasTermwiseCompletedConstantModel J I L :=
  sorry

/-- The completed constant complex of a bounded finite projective `Λ^∧`-complex,
with constant differentials, is a termwise completed-constant model. This is
`Q` of `constantAdicCompletionComplex`, i.e. the same derived object as
`ofConstantAdicCompletionComplex`. -/
theorem hasTermwiseCompletedConstantModel_of_constantAdicCompletionComplex
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ)
    [M.IsBoundedFiniteProjective] :
    HasTermwiseCompletedConstantModel J I
      (DerivedCategory.Q.obj ((constantAdicCompletionComplex J I).obj M)) :=
  sorry

end Derived

end AlgebraicGeometry.Scheme.ProEt

end
