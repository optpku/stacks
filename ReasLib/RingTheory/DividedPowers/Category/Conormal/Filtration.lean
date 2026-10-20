module

public import ReasLib.RingTheory.DividedPowers.FirstOrder
public import ReasLib.RingTheory.DividedPowers.Category.Conormal

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open DividedPowers

universe u

noncomputable section

namespace DividedPowerRing.Pushout

/-- The image in the conormal quotient of the fold-kernel part of the distinguished ideal. -/
def idealImage {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) :
    Submodule B (kernelQuotient f s₀ s₁ hpush) :=
  -- Local instance justification (defeq pin): s₀.toRingHom.toAlgebra is the canonical B-algebra induced by the pushout morphism, keeping restriction and quotient terms definitionally aligned.
  letI : Algebra B B₁ := s₀.toRingHom.toAlgebra
  let K := RingHom.ker (fold f s₀ s₁ hpush).toRingHom
  let L := K ^ 2 ⊔ B₁.dividedPowers.secondOrderIdeal K
  let Q := (L.restrictScalars B).comap (K.restrictScalars B).subtype
  Submodule.map Q.mkQ ((B₁.ideal.restrictScalars B).comap (K.restrictScalars B).subtype)

/-- Membership in the conormal image is represented by an element of the fold kernel lying in
the distinguished ideal, modulo the square and second-order relations. -/
theorem mem_idealImage_iff {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (x : kernelQuotient f s₀ s₁ hpush) :
    -- Local instance justification (defeq pin): s₀.toRingHom.toAlgebra is the canonical B-algebra induced by the pushout morphism, keeping membership and quotient terms definitionally aligned.
    letI : Algebra B B₁ := s₀.toRingHom.toAlgebra
    let K := RingHom.ker (fold f s₀ s₁ hpush).toRingHom
    let L := K ^ 2 ⊔ B₁.dividedPowers.secondOrderIdeal K
    let Q := (L.restrictScalars B).comap (K.restrictScalars B).subtype
    x ∈ idealImage f s₀ s₁ hpush ↔
      ∃ y : K, y.1 ∈ B₁.ideal ∧ Q.mkQ y = x := sorry

/-- The conormal comparison sends the generated divided-power differential submodule onto the
image of the fold kernel inside the distinguished ideal. -/
theorem kernelComparison_submodule {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B)
    (s₀ s₁ : B ⟶ B₁) (hpush : IsPushout f f s₀ s₁) :
    Submodule.map (kernelComparison f s₀ s₁ hpush)
        (DividedPowerDifferential.submodule f.toRingHom B.dividedPowers) =
      idealImage f s₀ s₁ hpush := sorry

end DividedPowerRing.Pushout

end
