/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.EtaleRestriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent

/-! # Derived internal Hom and passage from the Zariski to the étale site -/

public section

open CategoryTheory
open AlgebraicGeometry.Scheme.AssociatedModule
open RingedSite.Hom RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- The canonical comparison from the étale inverse image of Zariski derived sheaf internal
Hom to the étale derived internal Hom of the inverse images. -/
def comparison (X : Scheme.{u})
    (E F : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    (commSmallEtaleToZariskiDerived X).obj
        (InternalHom.obj (J := X.smallZariskiTopology)
          (O := StandardSmall.commStructureSheaf .zariski X) E F) ⟶
      InternalHom.obj (J := X.smallEtaleTopology)
        (O := StandardSmall.commStructureSheaf .etale X)
        ((commSmallEtaleToZariskiDerived X).obj E)
        ((commSmallEtaleToZariskiDerived X).obj F) :=
  @SheafOfModules.Pullback.DerivedInternalHom.comparison.{u + 1, u}
    _ _ inferInstance inferInstance X.smallZariskiTopology X.smallEtaleTopology
    inferInstance inferInstance
    (StandardTopology.Small.instCommHasWeakSheafify .zariski X)
    (StandardTopology.Small.instCommWEqualsLocallyBijective .zariski X)
    (StandardTopology.Small.instCommHasWeakSheafify .etale X)
    (StandardTopology.Small.instCommWEqualsLocallyBijective .etale X)
    (smallZariskiToSmallEtale X) inferInstance inferInstance
    (StandardSmall.commStructureSheaf .zariski X)
    (StandardSmall.commStructureSheaf .etale X)
    (commSmallEtaleToZariskiStructureSheafMap X) inferInstance
    (commSmallEtaleToZariski_pullback_exact X) E F

/-- Étale inverse image commutes with derived sheaf internal Hom when its source is
pseudo-coherent and its target is bounded below, or when its source is perfect. -/
theorem isIso_comparison (X : Scheme.{u})
    (E F : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))
    (h : (E.IsPseudoCoherent ∧
      (DerivedCategory.TStructure.t.plus : ObjectProperty _) F) ∨ E.IsPerfect) :
    IsIso (comparison X E F) := by
  sorry

end AlgebraicGeometry.Scheme.SiteRestriction
