/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Pullback of coherent module sheaves
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Module pullback along a morphism of locally Noetherian algebraic spaces
preserves coherence. -/
theorem isCoherent_le_inverseImage_pullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) :
    SheafOfModules.isCoherent (structureSheaf Y) ≤
      (SheafOfModules.isCoherent (structureSheaf X)).inverseImage
        (Modules.pullback f) :=
  sorry

namespace Modules

/-- Pullback of a coherent module along a morphism of locally Noetherian
algebraic spaces is coherent. -/
instance instIsCoherent_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (F : Y.Modules) [F.IsCoherent] :
    ((pullback f).obj F).IsCoherent :=
  isCoherent_le_inverseImage_pullback f F inferInstance

end Modules

namespace Coh

/-- Pullback of coherent modules along a morphism of locally Noetherian
algebraic spaces. -/
noncomputable def pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) :
    Coh Y ⥤ Coh X :=
  ObjectProperty.FullSubcategory.restrict (Modules.pullback f)
    (isCoherent_le_inverseImage_pullback f)

/-- The underlying module of a pulled-back coherent module is the ordinary
module pullback. -/
theorem pullback_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (M : Coh Y) :
    ((pullback f).obj M).obj = (Modules.pullback f).obj M.obj :=
  sorry

end Coh

end AlgebraicGeometry.AlgebraicSpace
