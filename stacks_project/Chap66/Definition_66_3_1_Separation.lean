module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase

/-!
# Absolute separation axioms for algebraic spaces

An algebraic space `X` over a scheme `S` is separated, locally separated, quasi-separated, or
Zariski locally quasi-separated in the absolute sense when the corresponding relative property
holds after viewing `X` as an algebraic space over the terminal scheme.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelySeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyLocallySeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyZariskiLocallyQuasiSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
