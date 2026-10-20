module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extending relative-dimension bounds from a dense open

A relative-dimension bound for a flat morphism of algebraic spaces locally of
finite type extends from a topologically dense open of the target when the
morphism is locally of finite presentation or the open inclusion is
quasi-compact.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE

/-- A flat morphism of algebraic spaces locally of finite type
has relative dimension at most `d` if it has that bound after base change to a
topologically dense open subspace, and either the morphism is locally of finite
presentation or the open inclusion is quasi-compact. -/
@[stacks 0878]
theorem of_restrict_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (V : OpenSubspace Y) (d : ℕ)
    (hV_dense : Dense V.pointsSet)
    [RelativeDimensionLE (pullback.snd f V.ι) d]
    (h_finitePresentation_or_quasiCompact :
      LocallyOfFinitePresentation f ∨ QuasiCompact V.ι) :
    RelativeDimensionLE f d :=
  sorry

/-- A flat morphism of algebraic spaces locally of finite type and locally of
finite presentation has relative dimension at most `d` if it has that bound
after base change to a topologically dense open subspace. -/
theorem of_restrict_of_flat_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    [LocallyOfFiniteType f] [LocallyOfFinitePresentation f]
    (V : OpenSubspace Y) (d : ℕ) (hV_dense : Dense V.pointsSet)
    [RelativeDimensionLE (pullback.snd f V.ι) d] :
    RelativeDimensionLE f d :=
  of_restrict_of_flat f V d hV_dense (Or.inl inferInstance)

/-- A flat morphism of algebraic spaces locally of finite type has relative
dimension at most `d` if it has that bound after base change to a
quasi-compact topologically dense open subspace. -/
theorem of_restrict_of_flat_of_quasiCompact {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    (V : OpenSubspace Y) (d : ℕ) (hV_dense : Dense V.pointsSet)
    [RelativeDimensionLE (pullback.snd f V.ι) d] [QuasiCompact V.ι] :
    RelativeDimensionLE f d :=
  of_restrict_of_flat f V d hV_dense (Or.inr inferInstance)

end AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE
