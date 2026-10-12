/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf

/-!
# Relative projective spectrum maps of algebraic spaces

A map of quasi-coherent graded `𝒪_X`-algebras induces an open domain, a morphism
from that domain over `X`, and degreewise twist comparisons. This packages that
triple on algebraic spaces, in parallel with scheme-level `RelativeProjMap`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of an open subspace is an open immersion. -/
instance OpenSubspace.instIsOpenImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

/-- A map between relative projective spectra of algebraic spaces consists of an open
domain, a morphism from that domain over the base algebraic space, and degreewise
comparisons of twists. -/
structure RelativeProjMap
    {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    (πP : P ⟶ X) (πQ : Q ⟶ X)
    (𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    (twistP : ℤ → P.Modules) (twistQ : ℤ → Q.Modules)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ) where
  /-- The open subspace on which the induced morphism is defined. -/
  domain : OpenSubspace Q
  /-- The induced morphism from the open domain. -/
  map : domain.X ⟶ P
  /-- The induced morphism commutes with the structural morphisms to the base. -/
  map_over_base : map ≫ πP = domain.ι ≫ πQ
  /-- The degreewise comparison from the pullback of the source twist to the pullback of
  the target twist along the domain inclusion. -/
  theta :
    ∀ n : ℤ,
      (Modules.pullback map).obj (twistP n) ⟶
        (Modules.pullback domain.ι).obj (twistQ n)

namespace RelativeProjMap

variable {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
variable {πP : P ⟶ X} {πQ : Q ⟶ X}
variable {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
variable {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}

/-- The underlying morphism of a relative projective spectrum map, regarded as a morphism
over the common base algebraic space. -/
def overHom (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ) :
    Over.mk (r.domain.ι ≫ πQ) ⟶ Over.mk πP :=
  Over.homMk r.map r.map_over_base

/-- The underlying arrow of `overHom r` is `r.map`. -/
theorem overHom_left (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ) :
    (overHom r).left = r.map :=
  sorry

/-- A relative projective spectrum map has an open-immersion domain inclusion and lies
over the base; the degreewise comparisons are the field `r.theta`. -/
theorem spec (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ) :
    IsOpenImmersion r.domain.ι ∧ r.map ≫ πP = r.domain.ι ≫ πQ :=
  sorry

end RelativeProjMap

end AlgebraicGeometry.AlgebraicSpace
