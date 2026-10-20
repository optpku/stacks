/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality

/-! # Finite cohomology of naive obstruction theories and openness of versality -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

/-- A naive obstruction theory has finite cohomology if its obstruction complexes
have finitely generated cohomology in every degree on finite-type affine objects. -/
def NaiveObstructionTheory.hasFiniteCohomology (𝒪 : NaiveObstructionTheory X) :
    Prop :=
  ∀ (ξ : ObjectOverAffineOpen X) (i : ℤ),
    LocallyOfFiniteType ξ.toS →
      Module.Finite ξ.carrier
        ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj
          (Minus.ι.obj (𝒪.complex ξ)))

/-- Finite cohomology is finite generation of each homology module of the
obstruction complex on every finite-type affine object. -/
theorem NaiveObstructionTheory.hasFiniteCohomology_iff
    (𝒪 : NaiveObstructionTheory X) :
    𝒪.hasFiniteCohomology ↔
      ∀ (ξ : ObjectOverAffineOpen X) (i : ℤ),
        LocallyOfFiniteType ξ.toS →
          Module.Finite ξ.carrier
            ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj
              (Minus.ι.obj (𝒪.complex ξ))) :=
  Iff.rfl

/-- A naive obstruction theory with finite cohomology has a finitely generated
homology module in each degree on any finite-type affine object. -/
theorem NaiveObstructionTheory.finite_homology
    {𝒪 : NaiveObstructionTheory X} (h : 𝒪.hasFiniteCohomology)
    (ξ : ObjectOverAffineOpen X) (hft : LocallyOfFiniteType ξ.toS) (i : ℤ) :
    Module.Finite ξ.carrier
      ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj
        (Minus.ι.obj (𝒪.complex ξ))) :=
  h ξ i hft

/-- A category fibred in groupoids over a locally Noetherian scheme satisfying
the strong Rim–Schlessinger condition satisfies openness of versality if it has
a naive obstruction theory with finite cohomology on finite-type affine objects. -/
theorem OpennessOfVersality.ofNaiveObstructionTheory
    (𝒪 : NaiveObstructionTheory X) (h_finite : 𝒪.hasFiniteCohomology) :
    OpennessOfVersality X :=
  sorry

end AlgebraicGeometry.GroupoidsOver
