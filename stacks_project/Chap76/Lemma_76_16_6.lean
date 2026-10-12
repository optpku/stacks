/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_14_6
public import stacks_project.Chap76.Lemma_76_15_4
public import stacks_project.Chap76.Lemma_76_16_4_FormallyEtale

/-!
# Characterizations of formally étale morphisms of algebraic spaces

A morphism of algebraic spaces is formally étale if and only if it is
formally unramified and the identity is a universal first-order thickening,
equivalently if the sheaf of relative differentials vanishes and the
associated ideal sheaf of every universal first-order thickening vanishes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The sheaf `C_{X/Y}` of a morphism `f : X ⟶ Y` of algebraic spaces vanishes
if the associated ideal sheaf of every universal first-order thickening of `X`
over `Y` vanishes. For a first-order thickening this ideal sheaf is the
conormal sheaf of `X` in that thickening, as in the identification
`C_{X/Y} = C_{X/X'}`. -/
def isZeroConormal {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {X' : AlgebraicSpace S} (i : X ⟶ X') (g : X' ⟶ Y) [IsUniversalFirstOrder i g],
    i ≫ g = f → IsZero (Hom.idealSheaf i)

/-- Unfolding of `isZeroConormal`. -/
theorem isZeroConormal_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    isZeroConormal f ↔
      ∀ {X' : AlgebraicSpace S} (i : X ⟶ X') (g : X' ⟶ Y)
        [IsUniversalFirstOrder i g],
        i ≫ g = f → IsZero (Hom.idealSheaf i) :=
  sorry

/-- The associated ideal sheaf of any universal first-order thickening of a
morphism with `isZeroConormal` vanishes. -/
theorem isZeroConormal_apply {S : Scheme.{u}} {X Y X' : AlgebraicSpace S}
    {f : X ⟶ Y} {i : X ⟶ X'} {g : X' ⟶ Y} [IsUniversalFirstOrder i g]
    (hfg : i ≫ g = f) (h : isZeroConormal f) :
    IsZero (Hom.idealSheaf i) :=
  sorry

/-- Under formal unramifiedness, `C_{X/Y} = 0` if and only if some universal
first-order thickening of `f` has vanishing associated ideal sheaf. -/
theorem isZeroConormal_iff_exists {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyUnramified f] :
    isZeroConormal f ↔
      ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (g : X' ⟶ Y),
        i ≫ g = f ∧ IsUniversalFirstOrder i g ∧ IsZero (Hom.idealSheaf i) :=
  sorry

namespace Hom

/-- A first-order thickening of algebraic spaces is an isomorphism if and only
if its associated ideal sheaf vanishes. -/
theorem isZero_idealSheaf_iff_isIso {S : Scheme.{u}} {Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') [IsFirstOrderThickening i] :
    IsZero (Hom.idealSheaf i) ↔ IsIso i :=
  sorry

end Hom

/-- Vanishing of `Ω[f]` together with `isZeroConormal f` is equivalent to formal
unramifiedness together with `isZeroConormal f`. -/
theorem isZero_relativeDifferentials_and_conormal_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsZero (Ω[f]) ∧ isZeroConormal f ↔
      FormallyUnramified f ∧ isZeroConormal f :=
  sorry

namespace FormallyUnramified

/-- For a formally unramified morphism, the identity is a universal first-order
thickening over the target if and only if `C_{X/Y}` vanishes. -/
theorem isUniversalFirstOrder_id_iff_isZeroConormal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [FormallyUnramified f] :
    IsUniversalFirstOrder (𝟙 X) f ↔ isZeroConormal f :=
  sorry

/-- For a formally unramified morphism, the identity is a universal first-order
thickening over the target if and only if every universal first-order
thickening of `f` is an isomorphism. -/
theorem isUniversalFirstOrder_id_iff_forall_isIso {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [FormallyUnramified f] :
    IsUniversalFirstOrder (𝟙 X) f ↔
      ∀ {X' : AlgebraicSpace S} (i : X ⟶ X') (g : X' ⟶ Y)
        [IsUniversalFirstOrder i g], i ≫ g = f → IsIso i :=
  sorry

end FormallyUnramified

namespace FormallyEtale

/-- Lemma 76.16.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally étale if and only if `f` is
formally unramified and the universal first-order thickening of `X` over `Y`
is the identity thickening `IsUniversalFirstOrder (𝟙 X) f`. -/
@[stacks 0614]
theorem iff_isUniversalFirstOrder_id {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔ FormallyUnramified f ∧ IsUniversalFirstOrder (𝟙 X) f :=
  sorry

/-- Lemma 76.16.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally étale if and only if `f` is
formally unramified and `C_{X/Y} = 0` in the sense of `isZeroConormal f`. -/
@[stacks 0614]
theorem iff_isZero_conormal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔ FormallyUnramified f ∧ isZeroConormal f :=
  sorry

/-- Lemma 76.16.6 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally étale if and only if
`Ω[f] = 0` and `C_{X/Y} = 0`. The second conjunct is defined because
`IsZero (Ω[f])` implies `FormallyUnramified f`, hence a universal first-order
thickening exists. -/
@[stacks 0614]
theorem iff_isZero_relativeDifferentials_and_conormal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallyEtale f ↔ IsZero (Ω[f]) ∧ isZeroConormal f :=
  sorry

/-- A formally étale morphism of algebraic spaces is formally unramified. -/
instance toFormallyUnramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [FormallyEtale f] :
    FormallyUnramified f :=
  sorry

/-- The identity morphism is a universal first-order thickening of a formally
étale morphism of algebraic spaces over the target. -/
instance instIsUniversalFirstOrder_id {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [FormallyEtale f] : IsUniversalFirstOrder (𝟙 X) f :=
  sorry

/-- A formally unramified morphism of algebraic spaces whose identity is a
universal first-order thickening over the target is formally étale. -/
instance of_isUniversalFirstOrder_id {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [FormallyUnramified f] [IsUniversalFirstOrder (𝟙 X) f] :
    FormallyEtale f :=
  sorry

end FormallyEtale

end AlgebraicGeometry.AlgebraicSpace
