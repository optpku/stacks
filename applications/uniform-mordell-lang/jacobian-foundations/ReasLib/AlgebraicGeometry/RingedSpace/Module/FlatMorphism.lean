module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat morphisms of ringed spaces

This file defines flatness for morphisms of ringed spaces, expressed stalkwise, and connects
to mathlib's canonical scheme-theoretic flatness predicate.

- `RingedSpace.Hom.FlatAt f x`: the stalk map at `x` is flat
- `RingedSpace.Hom.IsFlat f`: flat at every point
- `Scheme.Hom.isFlat_iff_flat`: bridge to `AlgebraicGeometry.Flat`
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open AlgebraicGeometry
open CategoryTheory

universe u

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- A morphism of ringed spaces is flat at `x` when the induced stalk map is flat. -/
@[stacks 02N3 "(1)"]
abbrev FlatAt (x : X) : Prop :=
  (f.hom.stalkMap x).hom.Flat

/-- A morphism of ringed spaces is flat when it is flat at every point. -/
@[mk_iff, stacks 02N3 "(2)"]
class IsFlat : Prop where
  flatAt (x : X) : FlatAt f x

/-- Flatness of a morphism of ringed spaces is equivalent to flatness at every source
point. -/
@[stacks 02N3 "stalkwise characterization"]
theorem IsFlat.iff_forall_flatAt :
    IsFlat f ↔ ∀ x : X, FlatAt f x := sorry

/-- A flat morphism is flat at every source point. -/
@[stacks 02N3 "pointwise projection"]
theorem IsFlat.atPoint [IsFlat f] (x : X) : FlatAt f x := sorry

/-- Stalkwise flatness at every source point constructs flatness of a morphism of ringed
spaces. -/
@[stacks 02N3 "stalkwise constructor"]
theorem IsFlat.of_forall_flatAt (h : ∀ x : X, FlatAt f x) : IsFlat f := sorry

namespace IsFlat

/-- The identity morphism of a ringed space is flat. -/
@[stacks 02N4 "identity"]
theorem id (X : RingedSpace.{u}) : IsFlat (𝟙 X) := sorry

/-- A composite of flat morphisms of ringed spaces is flat. -/
@[stacks 02N4 "composition"]
theorem comp {Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFlat f] [IsFlat g] : IsFlat (f ≫ g) := sorry

end IsFlat

end RingedSpace.Hom

namespace Scheme.Hom

open RingedSpace.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ringed-space flatness owner agrees with mathlib's scheme-theoretic flatness. -/
@[stacks 02N3 "scheme bridge"]
theorem isFlat_iff_flat :
    IsFlat f.toLRSHom.toShHom ↔ Flat f := sorry

/-- Scheme-theoretic flatness implies flatness of the underlying ringed-space morphism. -/
@[instance]
theorem isFlat_of_flat [Flat f] : IsFlat f.toLRSHom.toShHom :=
  (isFlat_iff_flat f).2 inferInstance

/-- Ringed-space flatness of a scheme morphism implies Mathlib's canonical scheme-theoretic
flatness predicate. This direction is explicit to avoid a typeclass-search loop. -/
theorem flat_of_isFlat [IsFlat f.toLRSHom.toShHom] : Flat f := sorry

end Scheme.Hom

namespace RingedSpace.Hom

open CategoryTheory CategoryTheory.Limits

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- Pullback along a flat morphism of ringed spaces is exact. -/
@[stacks 02N4]
theorem IsFlat.pullback_exact [IsFlat f] :
    exactFunctor _ _ (pullback f) := sorry

/-- Pullback along a flat morphism of ringed spaces preserves finite limits. -/
@[stacks 02N4 "preserves finite limits"]
theorem pullback_preservesFiniteLimits_of_isFlat [IsFlat f] :
    Limits.PreservesFiniteLimits (pullback f) := sorry

/-- Pullback along a flat morphism of ringed spaces preserves finite colimits. -/
@[stacks 02N4 "preserves finite colimits"]
theorem pullback_preservesFiniteColimits_of_isFlat [IsFlat f] :
    Limits.PreservesFiniteColimits (pullback f) := sorry

namespace IsFlat

/-- Flat pullback preserves finite limits. -/
@[stacks 02N4 "flat pullback preserves finite limits"]
theorem pullbackPreservesFiniteLimits [IsFlat f] :
    Limits.PreservesFiniteLimits (pullback f) := sorry

/-- Flat pullback preserves finite colimits. -/
@[stacks 02N4 "flat pullback preserves finite colimits"]
theorem pullbackPreservesFiniteColimits [IsFlat f] :
    Limits.PreservesFiniteColimits (pullback f) := sorry

/-- Pullback along a flat morphism, bundled as an exact functor. -/
@[stacks 02N4 "bundled exact flat pullback"]
noncomputable def exactPullback [IsFlat f] : Y.Modules ⥤ₑ X.Modules :=
  ⟨pullback f, IsFlat.pullback_exact f⟩

end IsFlat

section Pullback

variable {X Y Y' : RingedSpace.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- Flatness is stable under base change: the first projection of a pullback of a flat
morphism is flat. -/
@[stacks 02N4 "flatness stable under base change"]
theorem IsFlat.pullbackFst
    [HasPullback f g] [IsFlat g] :
    IsFlat (pullback.fst f g) := sorry

/-- Flatness is stable under base change in the other variable: the second projection of a
pullback of a flat morphism is flat. -/
@[stacks 02N4 "flatness stable under base change"]
theorem IsFlat.pullbackSnd
    [HasPullback f g] [IsFlat f] :
    IsFlat (pullback.snd f g) := sorry

end Pullback

end RingedSpace.Hom
