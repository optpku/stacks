/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closure properties of coherent module sheaves

The coherent module sheaves on a ringed site form a weak Serre class.  This file exposes the
atomic kernel, cokernel, extension, and finite-product consequences independently of ringed
spaces and textbook chapters.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace IsCoherent

/-- Coherence is invariant under isomorphism. -/
theorem ofIso {F G : SheafOfModules.{w} R} (e : F ≅ G) [G.IsCoherent] :
    F.IsCoherent := sorry

/-- A finite-type subobject of a coherent module sheaf is coherent. -/
@[stacks 01BY "(1)"]
theorem ofMono {F G : SheafOfModules.{w} R} (f : F ⟶ G)
    [Mono f] [F.IsFiniteType] [G.IsCoherent] : F.IsCoherent := sorry

/-- The kernel of a morphism from a finite-type module sheaf to a coherent module sheaf is
finite type. -/
@[stacks 01BY "(2)"]
instance kernelFiniteType {F G : SheafOfModules.{w} R} (f : F ⟶ G)
    [F.IsFiniteType] [G.IsCoherent] : (kernel f).IsFiniteType := sorry

/-- The kernel of a morphism between coherent module sheaves is coherent. -/
@[stacks 01BY "(3), kernel"]
theorem kernel {F G : SheafOfModules.{w} R} (f : F ⟶ G)
    [F.IsCoherent] [G.IsCoherent] : (Limits.kernel f).IsCoherent := sorry

/-- The cokernel of a morphism between coherent module sheaves is coherent. -/
@[stacks 01BY "(3), cokernel"]
theorem cokernel {F G : SheafOfModules.{w} R} (f : F ⟶ G)
    [F.IsCoherent] [G.IsCoherent] : (Limits.cokernel f).IsCoherent := sorry

/-- Coherence of the outer terms in a short exact sequence implies coherence of the middle term. -/
@[stacks 01BY "(4), middle term"]
theorem middle_of_shortExact {S : ShortComplex (SheafOfModules.{w} R)}
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₃.IsCoherent] : S.X₂.IsCoherent := sorry

/-- Coherence of the middle and right terms in a short exact sequence implies coherence of the left
term. -/
@[stacks 01BY "(4), left term"]
theorem left_of_shortExact {S : ShortComplex (SheafOfModules.{w} R)}
    (hS : S.ShortExact) [S.X₂.IsCoherent] [S.X₃.IsCoherent] : S.X₁.IsCoherent := sorry

/-- Coherence of the left and middle terms in a short exact sequence implies coherence of the right
term. -/
@[stacks 01BY "(4), right term"]
theorem right_of_shortExact {S : ShortComplex (SheafOfModules.{w} R)}
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] : S.X₃.IsCoherent := sorry

end IsCoherent

namespace isCoherent

/-- Coherent module sheaves form a weak Serre class. -/
@[stacks 01BY "(5)"]
instance isWeakSerreClass :
    IsWeakSerreClass (isCoherent R) := sorry

end isCoherent

end SheafOfModules
