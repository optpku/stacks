module

public import stacks_project.Chap76.Definition_76_3_1_Radicial
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Universally injective morphisms of algebraic spaces that are radicial

A universally injective morphism of algebraic spaces over a scheme is radicial
as soon as it is decent, quasi-separated, or locally separated.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Radicial

/-- Lemma 76.3.4 (1): a universally injective decent morphism of algebraic spaces
over a scheme is radicial. -/
@[stacks 0484]
instance of_universallyInjective_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyInjective f] [Decent f] : Radicial f :=
  sorry

/-- Lemma 76.3.4 (2): a universally injective quasi-separated morphism of algebraic
spaces over a scheme is radicial. -/
@[stacks 0484]
instance of_universallyInjective_of_quasiSeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [UniversallyInjective f] [QuasiSeparated f] :
    Radicial f :=
  sorry

/-- Lemma 76.3.4 (3): a universally injective locally separated morphism of algebraic
spaces over a scheme is radicial. -/
@[stacks 0484]
instance of_universallyInjective_of_locallySeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [UniversallyInjective f] [LocallySeparated f] :
    Radicial f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Radicial
