/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_11_2_Pushforward

/-!
# Restricted derived pushforward on algebraic spaces

Ambient derived pushforward along a quasi-compact, quasi-separated morphism
restricts to the full subcategory of complexes with quasi-coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

namespace pushforwardCohomologyIn

/-- Derived pushforward along a quasi-compact, quasi-separated morphism of algebraic
spaces preserves derived modules with quasi-coherent cohomology. -/
theorem mapsTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage
        (moduleDerivedPushforward f) :=
  sorry

end pushforwardCohomologyIn

/-- Ambient derived pushforward restricted to complexes with quasi-coherent cohomology. -/
noncomputable def pushforwardCohomologyIn {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    DerivedQCoh X ⥤ DerivedQCoh Y :=
  (derivedQuasiCoherentModuleProperty Y).lift
    (inclusion X ⋙ moduleDerivedPushforward f)
    (fun E ↦ pushforwardCohomologyIn.mapsTo f E.obj E.property)

namespace pushforwardCohomologyIn

/-- Forgetting the restricted ambient pushforward recovers ambient derived pushforward. -/
noncomputable def inclusionIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pushforwardCohomologyIn f ⋙ inclusion Y ≅
      inclusion X ⋙ moduleDerivedPushforward f :=
  (derivedQuasiCoherentModuleProperty Y).liftCompιIso
    (inclusion X ⋙ moduleDerivedPushforward f)
    (fun E ↦ mapsTo f E.obj E.property)

end pushforwardCohomologyIn

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
