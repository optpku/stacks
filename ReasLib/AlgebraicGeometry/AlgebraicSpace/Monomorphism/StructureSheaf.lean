module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom

/-!
# Quasi-compact monomorphisms with universally injective structure sheaf maps

A quasi-compact monomorphism of algebraic spaces whose structure sheaf map remains
injective after every base change is an isomorphism, hence representable by schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Monomorphisms

/-- A quasi-compact monomorphism of algebraic spaces over a scheme whose canonical
structure sheaf map is injective after every base change is an isomorphism. -/
theorem isIso_of_universallyInjectiveStructureSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Mono f]
    (h_injective : ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
      Mono (Modules.unitToPushforwardObjUnit (pullback.snd f g))) :
    IsIso f :=
  sorry

/-- A quasi-compact monomorphism of algebraic spaces over a scheme whose canonical
structure sheaf map is injective after every base change is representable by schemes. -/
theorem relativelyRepresentable_of_universallyInjectiveStructureSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Mono f]
    (h_injective : ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
      Mono (Modules.unitToPushforwardObjUnit (pullback.snd f g))) :
    yoneda.relativelyRepresentable f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Monomorphisms
