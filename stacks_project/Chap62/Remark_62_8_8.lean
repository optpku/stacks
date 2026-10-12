/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import stacks_project.Chap62.Remark_62_8_8_Counterexample
public import stacks_project.Chap62.Remark_62_8_8_Functor

/-!
# Remark 62.8.8

Representability of the functor of effective relative cycles on locally finite
type slices, its seminormal restriction, the weakly normal obstruction in
characteristic 2, and comparison of `h`-sheafifications.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RelativeCycle
open AffinePlaneDegreeTwo

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Remark 62.8.8 (1): there exist a locally Noetherian scheme `S`, a morphism
`f : X ⟶ S` locally of finite type, and `r : ℕ` such that the contravariant
functor sending a scheme `S'` locally of finite type over `S` to
`z^{eff}(S' ×_S X / S', r)` is not representable, since
`z(X'/S', r) = z(X'_red / S'_red, r)` via `groupReductionEquiv`. -/
@[stacks 0H5Y]
theorem effectiveFunctor_not_isRepresentable :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S) (_ : IsLocallyNoetherian S)
      (_ : LocallyOfFiniteType f) (r : ℕ),
      ¬ (effectiveFunctor f r).IsRepresentable :=
  sorry

/-- Remark 62.8.8 (2): if `S / Spec ℚ` is Nagata and `f` is projective, then
`S' ↦ z^{eff}(S' ×_S X / S', r)` is representable on seminormal schemes locally
of finite type over `S`. This is the content of Theorem 3.21 of Kollár–Rice–Chinburg. -/
@[stacks 0H5Y, instance]
instance effectiveFunctorSeminormal_isRepresentable {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [S.Over (Spec (CommRingCat.of (ULift.{u} ℚ)))] [Scheme.Nagata S] [Projective f]
    (r : ℕ) :
    (effectiveFunctorSeminormal f r).IsRepresentable :=
  sorry

/-- Remark 62.8.8 (6): if `f : X ⟶ S` is projective, then the `h`-sheafification
of `S' ↦ z^{eff}(S' ×_S X / S', r)` agrees with the `h`-sheafification of a
representable functor, as in Section 4.4 of Suslin–Voevodsky. The Chow variety
of Theorem 4.13 of Kollár–Rice–Chinburg only coarsely represents a related
functor and is not introduced as a second owner. -/
@[stacks 0H5Y]
theorem exists_isRepresentable_hSheafification_iso {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] [Projective f]
    (r : ℕ) :
    ∃ (G H : (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ Type u)
      (η : effectiveFunctor f r ⟶ H) (θ : G ⟶ H),
        G.IsRepresentable ∧
          Presheaf.IsSheafification (locallyOfFiniteTypeOverHTopology S) η ∧
          Presheaf.IsSheafification (locallyOfFiniteTypeOverHTopology S) θ :=
  sorry

end AlgebraicGeometry.RelativeCycle

namespace AlgebraicGeometry.Scheme

/-- Remark 62.8.8 (3): a locally Noetherian reduced scheme `T` is weakly normal
if and only if every birational universal homeomorphism `T' ⟶ T` has a section. -/
@[stacks 0H5Y]
theorem weaklyNormal_iff_section_of_birational_universalHomeomorphism
    (T : Scheme.{u}) [IsLocallyNoetherian T] [IsReduced T] :
    WeaklyNormal T ↔
      ∀ {T' : Scheme.{u}} (g : T' ⟶ T) [UniversalHomeomorphism g] [IsBirational g],
        ∃ s : T ⟶ T', s ≫ g = 𝟙 T :=
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.AffinePlaneDegreeTwo

/-- Remark 62.8.8 (4): in characteristic 2, the canonical `σ`-invariant relative
0-cycle `α` on `X_W / W` does not descend to an effective relative 0-cycle `β`
on `X ×_S Sym²_S(X) / Sym²_S(X)`. The obstruction is visible at the generic
point of the diagonal image `V = Spec(k[u₁², v₁²])`, where the putative fibre
would pull back to `2[the point with coordinates (u₁, v₂)]`. -/
@[stacks 0H5Y]
theorem not_exists_descentCycle_of_char_two (k : Type u) [Field k] [CharP k 2] :
    ¬ ∃ β : RelativeCycle.effective
          (pullback.snd (planeHom k) (symmetricSquareToBase k)) 0,
        (RelativeCycle.effectiveMapOfIsoOver (descentIso k).hom
            (descentIso_hom_over k) 0
            (RelativeCycle.effectiveBaseChange
              (pullback.snd (planeHom k) (symmetricSquareToBase k))
              (toSymmetricSquare k) 0 β) :
            RelativeCycle.Family (totalOnSquareHom k) 0) =
          canonicalPairCycle k :=
  sorry

/-- Remark 62.8.8 (5): in characteristic 2, the functor of effective relative
0-cycles of `𝔸²_k / Spec k` is not representable on weakly normal schemes
locally of finite type over `k`. -/
@[stacks 0H5Y]
theorem effectiveFunctorWeaklyNormal_not_isRepresentable (k : Type u) [Field k]
    [CharP k 2] :
    ¬ (RelativeCycle.effectiveFunctorWeaklyNormal (planeHom k) 0).IsRepresentable :=
  sorry

end AlgebraicGeometry.AffinePlaneDegreeTwo
