/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Representability
public import ReasLib.AlgebraicGeometry.RelativeCycle.AffinePlaneDegreeTwo
import StacksCheckRecall

/-!
# Remark 62.8.8

The effective relative-cycle presheaf on locally finite type test schemes is
invariant under simultaneous reduction of total space and base, and is therefore
not representable in general. For a projective morphism over a locally
Noetherian Nagata scheme over the rational numbers, its restriction to
seminormal test schemes is representable, as in KRC, Theorem 3.21.

The weak-normality section criterion is stated under the explicit convention
that the locally Noetherian target is reduced: every birational universal
homeomorphism to it must have a right section.

In characteristic two, the actual affine plane and its two-section pair cycle
give an obstruction even on weakly normal finite type test schemes. The
symmetric square is the spectrum of
k[u₁+u₂, u₁u₂, v₁+v₂, v₁v₂, u₁v₁+u₂v₂]. The pair cycle cannot descend
to it. On the generic point of the diagonal image
Spec(k[u₁²,v₁²]), descent would require a degree-two cycle whose pullback along
k(u₁²,v₁²) ⊂ k(u₁,v₁) is 2[(u₁,v₁)]. These consistent generic coordinates
correct the transcription in the explanatory source prose without changing
the actual two-section cycle.

This does not contradict KRC, Theorem 4.13: the Chow variety only coarsely
represents two related functors, only one of which agrees with this presheaf
for projective total space. Separately, SV, Section 4.4 identifies the
h-sheafification of this presheaf for projective morphisms with that of a
representable presheaf. Common sheafification is distinct from fine
representability.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RelativeCycle AffinePlaneDegreeTwo

noncomputable section

universe u

/- Remark 62.8.8: representability of effective relative cycles and its obstructions. -/
@[stacks 0H5Y] #check (AlgebraicGeometry.RelativeCycle.effectiveFunctor_not_isRepresentable :
  ∃ (X S : Scheme.{u}) (f : X ⟶ S) (_ : IsLocallyNoetherian S)
      (_ : LocallyOfFiniteType f) (r : ℕ),
      ¬ (effectiveFunctor f r).IsRepresentable)

#check (AlgebraicGeometry.RelativeCycle.effectiveFunctorSeminormal_isRepresentable :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [S.Over (Spec (CommRingCat.of (ULift.{u} ℚ)))] [Scheme.Nagata S] [Projective f]
    (r : ℕ),
    (effectiveFunctorSeminormal f r).IsRepresentable)

#check (AlgebraicGeometry.RelativeCycle.exists_isRepresentable_hSheafification_iso :
  ∀ {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] [Projective f]
    (r : ℕ),
    ∃ (G H : (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ Type u)
      (η : effectiveFunctor f r ⟶ H) (θ : G ⟶ H),
        G.IsRepresentable ∧
          Presheaf.IsSheafification (locallyOfFiniteTypeOverHTopology S) η ∧
          Presheaf.IsSheafification (locallyOfFiniteTypeOverHTopology S) θ)

#check (AlgebraicGeometry.Scheme.weaklyNormal_iff_section_of_birational_universalHomeomorphism :
  ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] [IsReduced T],
    Scheme.WeaklyNormal T ↔
      ∀ {T' : Scheme.{u}} (g : T' ⟶ T) [UniversalHomeomorphism g] [IsBirational g],
        ∃ s : T ⟶ T', s ≫ g = 𝟙 T)

#check (AlgebraicGeometry.AffinePlaneDegreeTwo.not_exists_descentCycle_of_char_two :
  ∀ (k : Type u) [Field k] [CharP k 2],
    ¬ ∃ β : RelativeCycle.effective
          (pullback.snd (planeHom k) (symmetricSquareToBase k)) 0,
        (RelativeCycle.effectiveMapOfIsoOver (descentIso k).hom
            (descentIso_hom_over k) 0
            (RelativeCycle.effectiveBaseChange
              (pullback.snd (planeHom k) (symmetricSquareToBase k))
              (toSymmetricSquare k) 0 β) :
            (totalOnSquareHom k).FiberCycleFamily 0) =
          canonicalPairCycle k)

#check (AlgebraicGeometry.AffinePlaneDegreeTwo.effectiveFunctorWeaklyNormal_not_isRepresentable :
  ∀ (k : Type u) [Field k]
    [CharP k 2],
    ¬ (RelativeCycle.effectiveFunctorWeaklyNormal (planeHom k) 0).IsRepresentable)
