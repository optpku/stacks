/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.ExteriorPower.FormWedge

@[expose] public section

universe u

namespace exteriorPower.form

variable (B : Type u) [CommRing B]

/-- A pure exterior form, including the degree-zero and degree-one conventions. -/
def pureForm {Ω : Type u} [AddCommGroup Ω] [Module B Ω] :
    (degree : ℕ) → (Fin degree → Ω) → exteriorPower.form B Ω degree
  | 0 => fun _ ↦ (1 : B)
  | 1 => fun entries ↦ entries 0
  | degree + 2 => exteriorPower.ιMulti B (degree + 2)

/-- Exterior multiplication is concatenation of pure exterior generators. -/
noncomputable def wedge {Ω : Type u} [AddCommGroup Ω] [Module B Ω]
    (left right : ℕ) : exteriorPower.form B Ω left →ₗ[B]
      exteriorPower.form B Ω right →ₗ[B] exteriorPower.form B Ω (right + left) :=
  (Nat.add_comm left right) ▸ CrystallineFormWedge.wedge B Ω left right

/-- Wedge multiplication on pure forms concatenates their entries. -/
theorem wedge_pureForm {Ω : Type u} [AddCommGroup Ω] [Module B Ω]
    (left right : ℕ) (first : Fin left → Ω) (second : Fin right → Ω) :
    wedge B left right (pureForm B left first) (pureForm B right second) =
      pureForm B (right + left)
        (Fin.append first second ∘ Fin.cast (Nat.add_comm right left)) := sorry

end exteriorPower.form

end
