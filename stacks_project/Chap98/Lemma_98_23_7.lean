/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Definition_98_23_5_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 98.23.7

A category fibred in groupoids over a locally Noetherian base, satisfying
(RS*) and equipped with a naive obstruction theory whose complexes `E_x`
have finitely generated cohomology on finite-type algebras, satisfies
openness of versality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

/-- The complexes `E_x` of a naive obstruction theory have finitely generated
cohomology groups for every pair `(A, x)` with `A` of finite type over `S`. -/
def NaiveObstructionTheory.hasFiniteCohomology (𝒪 : NaiveObstructionTheory X) :
    Prop :=
  ∀ (ξ : ObjectOverAffineOpen X) (i : ℤ),
    LocallyOfFiniteType ξ.toS →
      Module.Finite ξ.carrier
        ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj
          (Minus.ι.obj (𝒪.complex ξ)))

/-- Finite generation of the cohomology of `E_x` is `Module.Finite` on the
homology of `𝒪.complex` for finite-type algebras over `S`. -/
theorem NaiveObstructionTheory.hasFiniteCohomology_iff
    (𝒪 : NaiveObstructionTheory X) :
    𝒪.hasFiniteCohomology ↔
      ∀ (ξ : ObjectOverAffineOpen X) (i : ℤ),
        LocallyOfFiniteType ξ.toS →
          Module.Finite ξ.carrier
            ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj
              (Minus.ι.obj (𝒪.complex ξ))) :=
  sorry

/-- Finite generation of cohomology of `E_x` is `Module.Finite` on each
homology object of `𝒪.complex` for finite-type algebras over `S`. -/
theorem NaiveObstructionTheory.finite_homology
    {𝒪 : NaiveObstructionTheory X} (h : 𝒪.hasFiniteCohomology)
    (ξ : ObjectOverAffineOpen X) (hft : LocallyOfFiniteType ξ.toS) (i : ℤ) :
    Module.Finite ξ.carrier
      ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj
        (Minus.ι.obj (𝒪.complex ξ))) :=
  sorry

/-- Lemma 98.23.7. Let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume that `X` satisfies
(RS*) and that `X` has a naive obstruction theory. Then openness of versality
holds for `X` provided the complexes `E_x` of Definition 98.23.5 have finitely
generated cohomology groups for pairs `(A, x)` where `A` is of finite type over
`S`. -/
@[stacks 07YU]
theorem OpennessOfVersality.ofNaiveObstructionTheory
    (𝒪 : NaiveObstructionTheory X) (h_finite : 𝒪.hasFiniteCohomology) :
    OpennessOfVersality X :=
  sorry

end AlgebraicGeometry.GroupoidsOver
