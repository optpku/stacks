module

public import ReasLib.Topology.ExtremallyDisconnected.Maps
import StacksCheckRecall

@[expose] public section

universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
  [ExtremallyDisconnected Y]

/- Lemma 5.26.4: the source's separate surjectivity and closed-subspace minimality assumptions
assemble into `IsMinimalSurjective`; the shared theorem is cross-universe and does not need
compactness of the target. -/
@[stacks 08YL]
#check (fun {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f)
  (hminimal : ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y)) ↦
  ExtremallyDisconnected.isHomeomorph_of_minimalSurjective hf ⟨hsurj, hminimal⟩)
