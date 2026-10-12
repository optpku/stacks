/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.System

import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism criterion for finite ideal-power systems

The representative-level kernel/cokernel condition and its quotient-category bridge live here so
downstream files can import the criterion without importing a chapter.

@stack 0EGX
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace IadicFiniteModuleSystem

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {X Y : IadicFiniteModuleSystem A I}

namespace HomRepresentative

/-- The stagewise kernel of a representative map. -/
@[stacks 0EGX "stagewise kernel of a representative"]
abbrev levelKernel (f : HomRepresentative X Y)
    (n : AdmissibleLevel f.cutoff) :
    Submodule (stageRing A I n.1) (powerSubmodule f.cutoff X n.1) :=
  LinearMap.ker (f n.1 n.2)

/-- The stagewise cokernel of a representative map. -/
@[stacks 0EGX "stagewise cokernel of a representative"]
abbrev levelCokernel (f : HomRepresentative X Y)
    (n : AdmissibleLevel f.cutoff) :=
  torsionQuotient f.cutoff Y n.1 ⧸ LinearMap.range (f n.1 n.2)

/-- A representative has an eventual uniform stage-ideal torsion bound on kernels and
cokernels. -/
@[stacks 0EGX "eventual bounded kernel and cokernel for a representative"]
def HasUniformTorsionBound (f : HomRepresentative X Y) : Prop :=
  ∃ c' N : ℕ, ∃ hN : f.cutoff ≤ N,
    ∀ n : ℕ+, ∀ hn : N ≤ (n : ℕ),
      Module.IsTorsionBySet
          (stageRing A I n)
          (levelKernel f ⟨n, Nat.le_trans hN hn⟩)
          (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n)) ∧
      Module.IsTorsionBySet
          (stageRing A I n)
          (levelCokernel f ⟨n, Nat.le_trans hN hn⟩)
          (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n))

/-- The cutoff and representative presentation do not affect the boundedness condition. -/
@[stacks 0EGX "promotion invariance of representative bounds"]
theorem hasUniformTorsionBound_congr {f g : HomRepresentative X Y}
    (h : f ≈ g) : HasUniformTorsionBound f ↔ HasUniformTorsionBound g := sorry

end HomRepresentative

namespace Category

/-- A quotient-category morphism admits a representative with an eventual uniform
kernel/cokernel bound. -/
@[stacks 0EGX "eventual bounded kernel and cokernel in the quotient category"]
def HasBound
    (f : (quotient A I).obj X ⟶ (quotient A I).obj Y) : Prop :=
  ∃ f₀ : HomRepresentative X Y,
    (quotient A I).map f₀ = f ∧
      HomRepresentative.HasUniformTorsionBound f₀

/-- Lemma 15.101.7 (0EGX): a morphism in the quotient category of finite ideal-power systems is
an isomorphism exactly when its representative maps have eventually bounded kernels and cokernels. -/
@[stacks 0EGX "isomorphism criterion by eventual kernel-cokernel bounds"]
theorem isIso_iff_hasBound
    (f : (quotient A I).obj X ⟶ (quotient A I).obj Y) :
    IsIso f ↔ HasBound f := sorry

end Category

/-- A raw representative becomes an isomorphism in the quotient category exactly when its
stagewise kernels and cokernels have a uniform eventual torsion bound. -/
@[stacks 0EGX "representative-level isomorphism criterion"]
theorem HomRepresentative.isIso_quotientMap_iff (f : HomRepresentative X Y) :
    IsIso ((Category.quotient A I).map f) ↔ f.HasUniformTorsionBound := sorry

end IadicFiniteModuleSystem
