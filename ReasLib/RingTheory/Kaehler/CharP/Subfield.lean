/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.CharP
import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime-field Kähler maps to subfield-relative differentials

@stack 07P4

This leaf owns the canonical map `Ω[K⁄ZMod p] → Ω[K⁄k]` for a subfield `k ≤ K`.  The `ZMod p`
algebras and the compatible scalar tower are encapsulated in the data owner, because those
structures are canonical here but are intentionally not installed globally by Mathlib.  Consumers
therefore do not need local instance pins.
-/

@[expose] public section

universe u

namespace KaehlerDifferential.CharP.SubfieldMap

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]

/-- The canonical prime-field scalar tower through a subfield. -/
@[stacks 07P4 "prime-field scalar tower through a subfield"]
abbrev tower (k : Subfield K) :
    -- Local instance justification (instance diamond): Mathlib intentionally leaves the
    -- canonical `ZMod` algebra structures unregistered, so this owner pins them explicitly.
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : SMul (ZMod p) k := (inferInstance : Algebra (ZMod p) k).toSMul
    IsScalarTower (ZMod p) k K :=
  -- Local instance justification (instance diamond): this is the same canonical `ZMod` tower
  -- fixed in the result type, not a competing algebra structure.
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : SMul (ZMod p) k := (inferInstance : Algebra (ZMod p) k).toSMul
  IsScalarTower.of_algebraMap_eq
    (fun x =>
      congrArg (fun f : ZMod p →+* K => f x)
        (RingHom.ext_zmod ((algebraMap (ZMod p) K))
          ((algebraMap k K).comp (algebraMap (ZMod p) k))))

/-- The canonical map from prime-field differentials to differentials relative to a subfield. -/
@[stacks 07P4 "Kähler map relative to a subfield"]
noncomputable def map (k : Subfield K) :
    -- Local instance justification (instance diamond): the map's source and target require the
    -- deliberately non-global `ZMod` algebra structures and their fixed scalar tower.
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : SMul (ZMod p) k := (inferInstance : Algebra (ZMod p) k).toSMul
    letI : IsScalarTower (ZMod p) k K := tower k
    Ω[K⁄ZMod p] →ₗ[K] Ω[K⁄k] :=
  -- Local instance justification (instance diamond): repeat the exact pins from the result type
  -- while constructing the canonical Mathlib Kähler map.
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : SMul (ZMod p) k := (inferInstance : Algebra (ZMod p) k).toSMul
  letI : IsScalarTower (ZMod p) k K := tower k
  KaehlerDifferential.map (ZMod p) k K K

/-- The subfield-relative map sends a universal differential to the corresponding differential. -/
@[simp, stacks 07P4 "subfield-relative Kähler map on universal differentials"]
theorem map_D (k : Subfield K) (x : K) :
    -- Local instance justification (instance diamond): this statement computes the map under the
    -- same deliberately pinned `ZMod` algebra structures as `map`.
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : SMul (ZMod p) k := (inferInstance : Algebra (ZMod p) k).toSMul
    letI : IsScalarTower (ZMod p) k K := tower k
    map k (D (ZMod p) K x) = D k K x := sorry
/- Proof strategy: unfold `map` and apply `KaehlerDifferential.map_D`; the algebra map from the
subfield to `K` is the subtype inclusion. -/

end KaehlerDifferential.CharP.SubfieldMap
