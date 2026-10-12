/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.DerivedLimit
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology.UnderlyingComparison
import StacksCheckRecall

/-!
# Remark 15.88.2: derived inverse limits as derived global sections

@stack 091E
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem
open SheafOfModules.Cohomology

universe u

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)

/- Remark 15.88.2 (Stacks 091E): a ring sheaf on the chaotic site of `ℕ` has global sections
given by the inverse limit of its stage rings. -/
@[stacks 091E "global sections of a sequential ring system"] #check
  ((Sheaf.ΓNatIsoLim NatSite RingCat.{u}).app (sequentialRingSystemRingSheaf A ρ) :
    (Sheaf.Γ NatSite RingCat.{u}).obj (sequentialRingSystemRingSheaf A ρ) ≅
      limit (sequentialRingSystem A ρ ⋙ forget₂ CommRingCat RingCat))

/- Remark 15.88.2: the total right-derived inverse-limit functor is the reusable varying-ring
module owner. -/
@[stacks 091E "derived inverse limit as derived global sections"] #check
  @CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit.ringedModuleDerivedInverseLimitFunctor

/- Remark 15.88.2: cohomology computed in modules agrees with cohomology of the underlying
abelian groups by the general ringed-site comparison. -/
@[stacks 091E "module and underlying-group cohomology comparison"] #check
  @underlying_isomorphic
