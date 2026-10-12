/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.AffineBaseChange

/-!
# Picard groups under field extension

Pullback along a field extension is injective on the Picard group of a quasi-compact,
quasi-separated scheme with semilocal global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- Pullback on Picard groups along a field extension is injective when the source scheme is
quasi-compact and quasi-separated and has semilocal global sections. -/
@[stacks 0CC5]
theorem picardPullback_injective
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [Finite (MaximalSpectrum (Γ(X, ⊤)))] :
    Function.Injective (Scheme.Hom.picardPullback (FieldExtension.toSource k k' f)) := sorry

end AlgebraicGeometry.FieldExtension
