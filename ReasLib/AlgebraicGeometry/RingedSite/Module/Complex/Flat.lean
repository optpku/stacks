/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat

/-!
# Termwise-flat complexes of modules on a ringed site

The canonical owner is `HomologicalComplex.IsTermwiseFlat`.  This module provides the
ringed-site compatibility name and degreewise API; it does not introduce another class or
instance.  K-flatness remains a separate property of the total tensor complex.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace CochainComplex

/-- The ringed-site compatibility name for canonical termwise flatness of a cochain complex. -/
abbrev IsTermwiseFlat
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFlat K

namespace IsTermwiseFlat

/-- Every term of a termwise-flat complex is flat over the structure sheaf. -/
theorem isFlat
    {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (hK : IsTermwiseFlat K) (n : ℤ) : IsFlat 𝒪 (K.X n) := sorry

end IsTermwiseFlat

/-- A complex is termwise flat if its terms are flat degreewise. -/
theorem isTermwiseFlat_iff
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) :
    IsTermwiseFlat K ↔ ∀ n : ℤ, IsFlat 𝒪 (K.X n) := sorry

/-- Construct termwise flatness from an explicit degreewise flatness hypothesis. -/
theorem isTermwiseFlat_of_forall_isFlat
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (hK : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    IsTermwiseFlat K := sorry

end CochainComplex

end

end SheafOfModules.RingedSite
