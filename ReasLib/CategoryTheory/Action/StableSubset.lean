module

public import Mathlib.CategoryTheory.Action.Concrete

@[expose] public section

universe u

open CategoryTheory

namespace Action

variable {G : Type u} [Group G]

/-- The restriction of a bundled `G`-action to a `G`-stable subset of its carrier. -/
def ofStableSubset (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) : Action (Type u) G where
  V := O
  ρ :=
    { toFun g := ↾fun x ↦ ⟨U.ρ g x.1, hO g x.2⟩
      map_one' := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom U.ρ.map_one x.1
      map_mul' := by
        intro g h
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (U.ρ.map_mul g h) x.1 }

/-- The restricted action sends a subtype element to its ambient translate. -/
@[simp]
theorem ofStableSubset_ρ_apply (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) (g : G) (x : O) :
    (ofStableSubset U O hO).ρ g x = ⟨U.ρ g x.1, hO g x.2⟩ := rfl

/-- The subtype inclusion of a stable subset is an equivariant morphism. -/
def stableSubsetInclusion (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) :
    ofStableSubset U O hO ⟶ U where
  hom := ↾Subtype.val
  comm := fun _ ↦ rfl

/-- The underlying map of the stable-subset inclusion is `Subtype.val`. -/
@[simp]
theorem stableSubsetInclusion_apply (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) (x : O) :
    (stableSubsetInclusion U O hO).hom x = x.1 := rfl

/-- The inclusion of a `G`-stable subset is a monomorphism. -/
theorem stableSubsetInclusion_mono (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) :
    Mono (stableSubsetInclusion U O hO) := sorry

end Action
