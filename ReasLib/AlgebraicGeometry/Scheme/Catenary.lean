/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Catenary.Basic

/-!
# Catenary schemes

Criteria for scheme catenarity in terms of open covers and affine coordinate rings, together
with its preservation under immersions.
-/

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

/-- A scheme is catenary exactly when the section ring of every affine open is catenary. -/
theorem catenarySpace_iff_forall_affineOpen_isCatenaryRing (S : Scheme.{u}) :
    CatenarySpace S ↔ ∀ U : S.affineOpens, IsCatenaryRing Γ(S, U) := sorry

/-- A scheme is catenary exactly when all of its stalk rings are catenary. -/
@[simp]
theorem catenarySpace_iff_forall_isCatenaryRing_stalk (S : Scheme.{u}) :
    CatenarySpace S ↔ ∀ x : S, IsCatenaryRing (S.presheaf.stalk x) := sorry

namespace CatenarySpace

/-- Every stalk ring of a catenary scheme is catenary. -/
theorem isCatenaryRing_stalk {S : Scheme.{u}} (hS : CatenarySpace S) (x : S) :
    IsCatenaryRing (S.presheaf.stalk x) :=
  (catenarySpace_iff_forall_isCatenaryRing_stalk S).1 hS x

end CatenarySpace

/-- The stalk ring at every point of a catenary scheme is canonically catenary. -/
instance instIsCatenaryRingStalk (S : Scheme.{u}) [CatenarySpace S] (x : S) :
    IsCatenaryRing (S.presheaf.stalk x) :=
  CatenarySpace.isCatenaryRing_stalk (inferInstance : CatenarySpace S) x

/-- A scheme whose stalk rings are all catenary is catenary. -/
theorem catenarySpace_of_forall_isCatenaryRing_stalk (S : Scheme.{u})
    (hS : ∀ x : S, IsCatenaryRing (S.presheaf.stalk x)) : CatenarySpace S :=
  (catenarySpace_iff_forall_isCatenaryRing_stalk S).2 hS

/-- A scheme is catenary exactly when it has an affine open cover by spectra of catenary
section rings. -/
theorem catenarySpace_iff_exists_affineOpenCover_isCatenaryRing (S : Scheme.{u}) :
    CatenarySpace S ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsCatenaryRing Γ(S, (𝒰.f i).opensRange) := sorry

/-- Scheme catenarity, catenarity on an open cover, catenarity of all affine-open section rings,
and catenarity of the section rings on one affine open cover are equivalent. -/
theorem catenarySpace_tfae (S : Scheme.{u}) :
    List.TFAE
      [ CatenarySpace S,
        ∃ (ι : Type v) (U : ι → S.Opens), IsOpenCover U ∧ ∀ i, CatenarySpace (U i),
        ∀ U : S.affineOpens, IsCatenaryRing Γ(S, U),
        ∃ 𝒰 : S.AffineOpenCover,
          ∀ i : 𝒰.I₀, IsCatenaryRing Γ(S, (𝒰.f i).opensRange) ] := sorry

/-- The source of an immersion into a catenary scheme is catenary. -/
theorem catenarySpace_of_isImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] [CatenarySpace Y] : CatenarySpace X := sorry

end AlgebraicGeometry.Scheme
