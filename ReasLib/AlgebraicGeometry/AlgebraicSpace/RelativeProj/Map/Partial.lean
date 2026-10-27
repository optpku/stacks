/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Equality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

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

/-- Two partial relative-Proj maps are equivalent when a unique domain isomorphism
preserves their inclusions, morphisms, and all integral-degree comparisons. -/
def Equivalent (r s : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ) : Prop :=
  ∃! e : r.domain.X ≅ s.domain.X,
      ∃ (hι : e.hom ≫ s.domain.ι = r.domain.ι)
        (hmap : e.hom ≫ s.map = r.map),
        ∀ n : ℤ,
          (Modules.pullback e.hom).map (s.theta n) ≫
              (Modules.pullbackCompIso e.hom s.domain.ι ≪≫
                Modules.pullbackCongr hι).hom.app (twistQ n) =
            (Modules.pullbackCompIso e.hom s.map ≪≫
                Modules.pullbackCongr hmap).hom.app (twistP n) ≫ r.theta n

/-- Equivalence is the existence of a unique domain isomorphism preserving the
inclusions, morphisms, and comparison maps under canonical pullback transport. -/
theorem equivalent_iff (r s : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ) :
    Equivalent r s ↔ ∃! e : r.domain.X ≅ s.domain.X,
      ∃ (hι : e.hom ≫ s.domain.ι = r.domain.ι)
        (hmap : e.hom ≫ s.map = r.map),
        ∀ n : ℤ,
          (Modules.pullback e.hom).map (s.theta n) ≫
              (Modules.pullbackCompIso e.hom s.domain.ι ≪≫
                Modules.pullbackCongr hι).hom.app (twistQ n) =
            (Modules.pullbackCompIso e.hom s.map ≪≫
                Modules.pullbackCongr hmap).hom.app (twistP n) ≫ r.theta n :=
  by rfl

end RelativeProjMap

end AlgebraicGeometry.AlgebraicSpace
