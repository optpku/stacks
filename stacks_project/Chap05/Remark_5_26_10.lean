module

public import ReasLib.Topology.Category.Stonean.Minimal
import StacksCheckRecall

@[expose] public section

universe u

open Cardinal Function Set

/- Remark 5.26.10: a minimal Stonean cover has the double-power cardinal bound obtained from the
dense canonical section of its minimal surjection. -/
@[stacks 090E]
#check (fun {X : CompHaus.{u}} {X' : Stonean.{u}} (f : X'.compHaus ⟶ X)
  (hsurj : Surjective f)
  (hminimal : ∀ Z : Set X', Z ≠ (Set.univ : Set X') → IsClosed Z → f '' Z ≠ (Set.univ : Set X))
  (κ : Cardinal.{u}) (_hκ_infinite : ℵ₀ ≤ κ) (hκX : Cardinal.mk X ≤ κ) ↦
  CompHaus.MinimalStoneanCover.cardinalMk_le_doublePower
    { space := X', π := f, minimal := ⟨hsurj, hminimal⟩ } κ hκX)
