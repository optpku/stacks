module

public import stacks_project.Chap104.Lemma_104_3_2_Comparison
public import stacks_project.Chap104.«104_3_2_1»
import StacksCheckRecall

/-!
# Lemma 104.3.2

With the assumptions and notation of Lemma 103.15.1, the identities
`g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹` and `L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!`
hold on unbounded derived categories of modules and of abelian sheaves.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]
variable (φ : X ⟶ Y)

section Smooth

variable [Smooth φ]

/-- Lemma 104.3.2 (1): with the assumptions and notation of Lemma 103.15.1,
the identity `g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹` holds on unbounded derived
categories of modules for a smooth 1-morphism, as invertibility of the
canonical mate `Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*` on the lisse-étale square. -/
@[stacks 07AV]
instance lisseEtaleDerivedPushforwardRestrictionComparison.instIsIso :
    IsIso (lisseEtaleDerivedPushforwardRestrictionComparison φ) := sorry

/-- Lemma 104.3.2 (2): with the assumptions and notation of Lemma 103.15.1,
the identity `g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹` holds on unbounded derived
categories of abelian sheaves for a smooth 1-morphism, as invertibility of
the canonical mate `Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*` on the lisse-étale square. -/
@[stacks 07AV]
instance lisseEtaleAbelianDerivedPushforwardRestrictionComparison.instIsIso :
    IsIso (lisseEtaleAbelianDerivedPushforwardRestrictionComparison φ) :=
  sorry

end Smooth

section Flat

variable [Flat φ]

/-- Lemma 104.3.2 (3): with the assumptions and notation of Lemma 103.15.1,
the identity `g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹` holds on unbounded derived
categories of modules for a flat 1-morphism, as invertibility of the
canonical mate `Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*` on the flat-fppf square. -/
@[stacks 07AV]
instance flatFppfDerivedPushforwardRestrictionComparison.instIsIso :
    IsIso (flatFppfDerivedPushforwardRestrictionComparison φ) := sorry

/-- Lemma 104.3.2 (4): with the assumptions and notation of Lemma 103.15.1,
the identity `g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹` holds on unbounded derived
categories of abelian sheaves for a flat 1-morphism, as invertibility of the
canonical mate `Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*` on the flat-fppf square. -/
@[stacks 07AV]
instance flatFppfAbelianDerivedPushforwardRestrictionComparison.instIsIso :
    IsIso (flatFppfAbelianDerivedPushforwardRestrictionComparison φ) := sorry

end Flat

/- Lemma 104.3.2 (5): with the assumptions and notation of Lemma 103.15.1,
the identity `L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!` holds on unbounded derived
categories of modules for a smooth 1-morphism of algebraic stacks. -/
@[stacks 07AV]
#check lisseEtaleDerivedLowerShriekComparison.isIso

/- Lemma 104.3.2 (6): with the assumptions and notation of Lemma 103.15.1,
the identity `L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!` holds on unbounded derived
categories of abelian sheaves for a smooth 1-morphism of algebraic stacks. -/
@[stacks 07AV]
#check lisseEtaleAbelianDerivedLowerShriekComparison.isIso

/- Lemma 104.3.2 (7): with the assumptions and notation of Lemma 103.15.1,
the identity `L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!` holds on unbounded derived
categories of modules for a flat 1-morphism of algebraic stacks. -/
@[stacks 07AV]
#check flatFppfDerivedLowerShriekComparison.isIso

/- Lemma 104.3.2 (8): with the assumptions and notation of Lemma 103.15.1,
the identity `L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!` holds on unbounded derived
categories of abelian sheaves for a flat 1-morphism of algebraic stacks. -/
@[stacks 07AV]
#check flatFppfAbelianDerivedLowerShriekComparison.isIso

end AlgebraicGeometry.AlgebraicStack
