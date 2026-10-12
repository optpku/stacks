/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Duality
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness from an exact pairing

An exact left-duality pairing in the derived category of a ring forces the paired object to be
perfect.  The tensor-unit comparison is explicit because the selected derived presentation need
not be definitionally the monoidal unit.

@stack 0FNS
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory.InternalHom

universe u

namespace CategoryTheory.DerivedCategory.IsPerfect

variable {R : Type u} [CommRing R]
variable [MonoidalCategory (DerivedCategory (ModuleCat R))]

/-- Lemma 15.127.3 (0FNS): an exact pairing with `M` implies that `M` is perfect. -/
@[stacks 0FNS "Perfectness from an exact pairing"]
theorem of_exactPairing
    (s : ((ModuleCat.single0 (ModuleCat.of R R)) :
      DerivedCategory (ModuleCat R)) ≅ 𝟙_ (DerivedCategory (ModuleCat R)))
    {M N : DerivedCategory (ModuleCat R)}
    (hpair : ExactPairing N M) :
    M.IsPerfect := sorry
-- Proof strategy: use `hpair` to identify the represented Hom functor of `M` with the tensor of
-- the represented Hom functor of the compact unit by `N`; tensoring by a left dual preserves
-- coproducts, hence `M` is compact, and the perfect/compact characterization of `D(R)` concludes.

end CategoryTheory.DerivedCategory.IsPerfect

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]
variable [MonoidalCategory (DerivedCategory (ModuleCat R))]
variable [BraidedCategory (DerivedCategory (ModuleCat R))]
variable [RHom.Has (A := R)]
variable [DerivedTensor.Right.Has (C := ModuleCat R)]

local notation "DMod" => DerivedCategory (ModuleCat R)

/-- Lemma 15.127.3 (0FNS), equivalence of (1) and (2): an object of `D(R)` has a left
dual if and only if it is perfect. -/
@[stacks 0FNS "left-dualizable iff perfect"]
theorem isLeftDualizable_iff_isPerfect
    (C : RHom.ClosedComparison (A := R))
    (s : RHom.Unit.single (A := R) ≅ 𝟙_ DMod)
    (M : DMod) :
    IsLeftDualizable M ↔ M.IsPerfect := sorry
-- Proof strategy: the forward implication applies `IsPerfect.of_exactPairing` to a chosen left
-- dual.  For the reverse implication, use the canonical derived dual `dual M`, the closed
-- comparison `C`, and the unit isomorphism `s` to construct its exact pairing with a perfect `M`.

/-- Lemma 15.127.3 (0FNS), source form of the equivalence: an object of `D(R)` is perfect
if and only if it admits an exact pairing with some derived object. -/
@[stacks 0FNS "exact-pairing existence iff perfect"]
theorem exists_exactPairing_iff_isPerfect
    (C : RHom.ClosedComparison (A := R))
    (s : RHom.Unit.single (A := R) ≅ 𝟙_ DMod)
    (M : DMod) :
    (∃ N : DMod, Nonempty (ExactPairing N M)) ↔ M.IsPerfect := sorry
-- Proof strategy: rewrite existence of an `ExactPairing N M` as left dualizability of `M`, then
-- apply `isLeftDualizable_iff_isPerfect`; in the reverse direction use the canonical derived dual
-- as the witness rather than choosing an unrelated object.

namespace Perfect.Duality

/-- Lemma 15.127.3 (0FNS), canonical dual: any chosen left dual of `M` is canonically
isomorphic to the derived dual `RHom(M, R[0])`. -/
@[stacks 0FNS "canonical left dual"]
noncomputable def leftDualIso
    (C : RHom.ClosedComparison (A := R))
    (s : RHom.Unit.single (A := R) ≅ 𝟙_ DMod)
    {M N : DMod} (p : ExactPairing N M) :
    N ≅ dual (A := R) M :=
  -- Local instance justification (noncanonical choice): use the closed owner recorded by `C`
  -- only while forming the canonical closed-dual comparison.
  letI : MonoidalClosed DMod := C.closed
  MonoidalClosed.Dual.leftDualIso p ≪≫
    ((MonoidalClosed.ihomOf C.closed M).mapIso s).symm ≪≫
    (C.objIso M (RHom.Unit.single (A := R))).symm

end Perfect.Duality

end CategoryTheory.DerivedCategory
