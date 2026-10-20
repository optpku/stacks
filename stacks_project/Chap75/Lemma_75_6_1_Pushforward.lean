module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_4_4_Pullback
public import stacks_project.Chap67.Lemma_67_8_4_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward

/-!
# Restricted derived pushforward on algebraic spaces

Ambient derived pushforward along a quasi-compact, quasi-separated morphism
restricts to the full subcategory of complexes with quasi-coherent cohomology,
and has a uniform cohomological bound after arbitrary base change when the
target is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Ambient derived pushforward `Rf_*`, restricted to complexes with quasi-coherent
cohomology. -/
noncomputable abbrev pushforward (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    DerivedQCoh X ⥤ DerivedQCoh Y :=
  pushforwardCohomologyIn f

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
