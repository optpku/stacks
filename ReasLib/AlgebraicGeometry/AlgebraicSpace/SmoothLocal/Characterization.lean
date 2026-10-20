module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Precoverage
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Characterizations of smooth locality on source-and-target

A morphism property of algebraic spaces that is smooth local on
source-and-target may be checked on a surjective-left smooth square, on every
smooth comparison into a smooth base change, or on smooth source and target
covers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))

/-- A morphism has a smooth-local-on-source-and-target property if and only if
the property holds on the top arrow of some commutative square with smooth
vertical arrows whose left vertical arrow is surjective. -/
theorem iff_exists_surjective_square [IsSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔
      ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
        Smooth a ∧ Smooth b ∧ Surjective a ∧ CommSq h a b f ∧ P h :=
  sorry

/-- A morphism has a smooth-local-on-source-and-target property if and only if
the top arrow of every commutative square with smooth right vertical arrow and
smooth comparison `U ⟶ pullback f b` has the property. -/
theorem iff_forall_comparison [IsSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔
      ∀ {U V : AlgebraicSpace S} (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
        (sq : CommSq h a b f),
        Smooth b → Smooth (pullback.lift a h sq.w.symm) → P h :=
  sorry

/-- A morphism has a smooth-local-on-source-and-target property if and only if
the property holds after base change along every member of some smooth covering
of the target. -/
theorem iff_exists_targetCover [IsSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (precoverage (@Smooth S)).ZeroHypercover.{u} Y,
      ∀ i : 𝒰.I₀, P (pullback.snd f (𝒰.f i)) :=
  sorry

/-- A morphism has a smooth-local-on-source-and-target property if and only if
every member of some smooth covering of the source has the property after
composition with the morphism. -/
theorem iff_exists_sourceCover [IsSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (precoverage (@Smooth S)).ZeroHypercover.{u} X,
      ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f) :=
  sorry

/-- A morphism has a smooth-local-on-source-and-target property if and only if,
after some smooth covering of the target, each base change admits a smooth
source covering whose composites to the target-cover member have the
property. -/
theorem iff_exists_targetSourceCovers [IsSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (precoverage (@Smooth S)).ZeroHypercover.{u} Y, ∀ i : 𝒰.I₀,
      ∃ 𝒱 : (precoverage (@Smooth S)).ZeroHypercover.{u} (pullback f (𝒰.f i)),
        ∀ j : 𝒱.I₀, P (𝒱.f j ≫ pullback.snd f (𝒰.f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget
