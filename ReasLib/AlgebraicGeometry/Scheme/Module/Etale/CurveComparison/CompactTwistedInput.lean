/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactFiniteInput

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inverse twist uses an actual coefficient-unit character. An open
kernel ensures discreteness; the geometric specialization must supply the
actual cyclotomic character and its continuity, not an arbitrary character. -/
def inverseCharacterTwist (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G))
    (M : DiscreteModuleCat Λ G) : DiscreteModuleCat Λ G :=
  ⟨{ V := M.obj.V
     ρ :=
       { toFun := fun g ↦ ModuleCat.ofHom
           ((LinearMap.lsmul Λ M.obj.V ((χ g)⁻¹ : Λˣ)).comp (M.obj.ρ g).hom)
         map_one' := by sorry
         map_mul' := by sorry } }, by
    -- The stabilizer contains the intersection of ker χ with the original
    -- open stabilizer; this uses hχ for this SAME χ.
    sorry⟩

theorem inverseCharacterTwist_action (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G))
    (M : DiscreteModuleCat Λ G) (g : G) (m : M.obj.V) :
    ((inverseCharacterTwist Λ G χ hχ M).obj.ρ g).hom m =
      (((χ g)⁻¹ : Λˣ) : Λ) • (M.obj.ρ g).hom m := rfl

/-- The finite input retains its carrier, hence finiteness is inherited. -/
instance inverseCharacterTwist_finite (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G))
    (M : DiscreteModuleCat Λ G) [Finite M.obj.V] :
    Finite (inverseCharacterTwist Λ G χ hχ M).obj.V :=
  inferInstanceAs (Finite M.obj.V)

/-- Explicit dual-action rule: dualizing the inverse twist produces the
positive character, with the original contragredient action g⁻¹. -/
theorem inverseTwist_dual_action (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G))
    (M : DiscreteModuleCat Λ G) [Finite M.obj.V] (g : G)
    (φ : (continuousDual Λ G
      (finiteCompactification Λ G (inverseCharacterTwist Λ G χ hχ M))).obj.V)
    (m : M.obj.V) :
    finiteCharacterInclusion Λ G (inverseCharacterTwist Λ G χ hχ M)
      (((continuousDual Λ G
        (finiteCompactification Λ G (inverseCharacterTwist Λ G χ hχ M))).obj.ρ g).hom φ) m =
      finiteCharacterInclusion Λ G (inverseCharacterTwist Λ G χ hχ M) φ
        (((χ g : Λˣ) : Λ) • (M.obj.ρ g⁻¹).hom m) := by sorry

/-- Connected evaluation for the ACTUAL inverse-twisted coefficient. This
only builds the algebraic/topological side; it is not the geometric trace map. -/
def inverseTwistedHomologyPairing (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G))
    (M : DiscreteModuleCat Λ G) [Finite M.obj.V] (i : ℕ) :=
  finiteHomologyPairing Λ G (inverseCharacterTwist Λ G χ hχ M) i

end CompactRepresentation
