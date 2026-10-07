module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic
public import ReasLib.CategoryTheory.Linear.PrincipalPower.ModuleCat
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Principal completion of cohomology on affine ideal complements

The quotient projections define a canonical comparison from complement cohomology to the
inverse limit of the cohomology of positive principal-power quotients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IdealComplement

variable {A : Type u} [CommRing A]

/-- Degree-`p` cohomology of associated module sheaves on `Spec A ∖ V(𝔞)`, with scalars
restricted to `A`. -/
noncomputable def tildeCohomologyFunctor (𝔞 : Ideal A) (p : ℕ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  let U := idealComplementOpens 𝔞
  tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor U.ι ⋙
    (RingedSpace.moduleSectionsEvaluationFunctor U.toScheme.toRingedSpace ⊤).rightDerived p ⋙
    ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap U.ι)

/-- The inverse system whose stage `n` is the degree-`p` cohomology on
`Spec A ∖ V(𝔞)` of the associated sheaf of `M ⧸ f ^ (n + 1) M`. -/
noncomputable def positiveCohomologySystem (𝔞 : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (p : ℕ) : SequentialInverseSystem (ModuleCat.{u} A) :=
  ModuleCat.PrincipalPower.quotientSystem f M ⋙ tildeCohomologyFunctor 𝔞 p

/-- Stage `n` of the positive principal-power cohomology system is the cohomology of the
associated sheaf of the corresponding quotient module. -/
theorem positiveCohomologySystem_obj (𝔞 : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (p n : ℕ) :
    (positiveCohomologySystem 𝔞 f M p).obj (op n) =
      (tildeCohomologyFunctor 𝔞 p).obj (ModuleCat.PrincipalPower.quotientStage f M n) := sorry

/-- The degree-`p` cohomology map induced by the quotient
`M ⟶ M ⧸ f ^ (n + 1) M`. -/
noncomputable def cohomologyProjection (𝔞 : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (p n : ℕ) :
    (tildeCohomologyFunctor 𝔞 p).obj M ⟶
      (positiveCohomologySystem 𝔞 f M p).obj (op n) :=
  (tildeCohomologyFunctor 𝔞 p).map
    (ModuleCat.ofHom (ModuleCat.PrincipalPower.submodule f M (n + 1)).mkQ)

/-- The cohomology projections commute with the transitions of the positive
principal-power quotient system. -/
theorem cohomologyProjection_naturality (𝔞 : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (p n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj ((tildeCohomologyFunctor 𝔞 p).obj M)).map
        (homOfLE (Nat.le_add_right n 1)).op ≫ cohomologyProjection 𝔞 f M p n =
      cohomologyProjection 𝔞 f M p (n + 1) ≫
        (positiveCohomologySystem 𝔞 f M p).map
          (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from the cohomology of `M̃` on `Spec A ∖ V(𝔞)` to the
cohomology of its positive principal-power quotients. -/
noncomputable def cohomologyCone (𝔞 : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (p : ℕ) : Cone (positiveCohomologySystem 𝔞 f M p) where
  pt := (tildeCohomologyFunctor 𝔞 p).obj M
  π := NatTrans.ofOpSequence (cohomologyProjection 𝔞 f M p)
    (cohomologyProjection_naturality 𝔞 f M p)

/-- The canonical morphism from the cohomology of `M̃` on `Spec A ∖ V(𝔞)` to
the inverse limit of the cohomology of its positive principal-power quotients. -/
noncomputable def cohomologyComparison (𝔞 : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (p : ℕ) :
    (tildeCohomologyFunctor 𝔞 p).obj M ⟶ limit (positiveCohomologySystem 𝔞 f M p) :=
  limit.lift _ (cohomologyCone 𝔞 f M p)

/-- Composing the cohomology comparison with the `n`th limit projection gives the
corresponding quotient-cohomology projection. -/
theorem cohomologyComparison_π (𝔞 : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (p n : ℕ) :
    cohomologyComparison 𝔞 f M p ≫
        limit.π (positiveCohomologySystem 𝔞 f M p) (op n) =
      cohomologyProjection 𝔞 f M p n := sorry

/-- Over a Noetherian `f`-adically complete ring, the complement-cohomology comparison for a
finite module is bijective in degrees below `s` if a power of `f` annihilates each local
cohomology module through degree `s + 1`. -/
@[stacks 0EKM]
theorem cohomologyComparison_bijective_of_localCohomology [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    [IsAdicComplete (Ideal.span {f}) A]
    (s i : ℕ)
    (h_ann : ∀ j : ℕ, j ≤ s + 1 →
      Module.IsAnnihilatedByPower (Ideal.span {f}) ((localCohomology 𝔞 j).obj M))
    (hi : i < s) :
    Function.Bijective (cohomologyComparison 𝔞 f M i) := sorry

end AlgebraicGeometry.Scheme.Modules.IdealComplement
