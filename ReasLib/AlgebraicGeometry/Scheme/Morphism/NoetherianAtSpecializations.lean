module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Noetherian

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A scheme morphism has `NoetherianAtSpecializations` when every target point
specializing from an image point has a Noetherian stalk. -/
def NoetherianAtSpecializations : MorphismProperty Scheme.{u} :=
  fun _ Y f ↦ ∀ (x : _) (y : Y), f x ⤳ y → IsNoetherianRing (Y.presheaf.stalk y)

namespace NoetherianAtSpecializations

/-- Membership in `NoetherianAtSpecializations` is equivalent to the pointwise
specialization-stalk condition. -/
theorem iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NoetherianAtSpecializations f ↔
      ∀ (x : X) (y : Y), f x ⤳ y → IsNoetherianRing (Y.presheaf.stalk y) := sorry

/-- The target stalk at a specialization of an image point is Noetherian. -/
theorem stalk {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : NoetherianAtSpecializations f)
    (x : X) (y : Y) (hxy : f x ⤳ y) :
    IsNoetherianRing (Y.presheaf.stalk y) := sorry

/-- The property `NoetherianAtSpecializations` is invariant under isomorphisms of
source and target. -/
instance instRespectsIso :
    MorphismProperty.RespectsIso (NoetherianAtSpecializations : MorphismProperty Scheme.{u}) :=
  sorry

/-- The property `NoetherianAtSpecializations` is étale local on the target. -/
instance instIsLocalAtTargetEtale :
    NoetherianAtSpecializations.IsLocalAtTarget Scheme.etalePrecoverage := sorry

/-- The property `NoetherianAtSpecializations` is étale local on the source. -/
instance instIsLocalAtSourceEtale :
    NoetherianAtSpecializations.IsLocalAtSource Scheme.etalePrecoverage := sorry

end NoetherianAtSpecializations

end AlgebraicGeometry
