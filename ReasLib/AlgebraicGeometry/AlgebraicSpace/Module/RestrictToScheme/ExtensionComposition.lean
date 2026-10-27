/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Quasicoherent

/-! # Actual comparisons for a composite represented-scheme pullback -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T Z : Over S}

/-- Extension/pullback comparison followed by the actual composition isomorphism. -/
def extensionCompositePullbackIso (g : ofOver Z ⟶ X) (t : T ⟶ Z)
    (M : X.Modules) [M.IsQuasicoherent] :
    (extension T).obj ((Scheme.Modules.pullback t.left).obj
      ((Modules.restrictToScheme Z).obj ((Modules.pullback g).obj M))) ≅
        (Modules.pullback (ofOverMap t ≫ g)).obj M := 
  @asIso _ _ _ _ (extensionPullbackComparison t ((Modules.pullback g).obj M))
    (@extensionPullbackComparison_isIso S T Z t ((Modules.pullback g).obj M)
      (pullbackIsQuasicoherent g M)) ≪≫
    (Modules.pullbackCompIso (ofOverMap t) g).app M

/-- Restriction/pullback comparison followed by composition. The map is defined
for every module; only its invertibility below uses QCoh. -/
def compositePullbackComparison (g : ofOver Z ⟶ X) (t : T ⟶ Z) (M : X.Modules) :
    (Scheme.Modules.pullback t.left).obj
      ((Modules.restrictToScheme Z).obj ((Modules.pullback g).obj M)) ⟶
        (Modules.restrictToScheme T).obj ((Modules.pullback (ofOverMap t ≫ g)).obj M) :=
  pullbackComparison t ((Modules.pullback g).obj M) ≫
    (Modules.restrictToScheme T).map ((Modules.pullbackCompIso (ofOverMap t) g).hom.app M)

/-- The specified composite comparison is invertible on quasi-coherent inputs. -/
instance compositePullbackComparison_isIso (g : ofOver Z ⟶ X) (t : T ⟶ Z)
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (compositePullbackComparison g t M) :=
  (compositePullbackIso g t M).isIso_hom


end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
