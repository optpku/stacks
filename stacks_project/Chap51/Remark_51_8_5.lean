/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

variable {U X : Scheme.{u}}

section

variable [IsLocallyNoetherian U] [IsLocallyNoetherian X]
variable (j : U ⟶ X) [IsOpenImmersion j] (x : U)

/- Remark 51.8.5 (1): the canonical map between reduced point closures makes the
square with `ι x`, `ι (j x)`, and the open immersion `j` commute. -/
@[stacks 0BK2] #check
  (AlgebraicGeometry.Scheme.PointClosure.map_ι j x :
    AlgebraicGeometry.Scheme.PointClosure.map j x ≫
        AlgebraicGeometry.Scheme.PointClosure.ι (j x) =
      AlgebraicGeometry.Scheme.PointClosure.ι x ≫ j)

/- Remark 51.8.5 (2): the two composite pushforwards of the structure sheaf of the
reduced point closure are canonically isomorphic. -/
@[stacks 0BK2] #check
  (AlgebraicGeometry.Scheme.PointClosure.pushforwardStructureSheafIso j x :
    (Scheme.Modules.pushforward j).obj
        (closedSubschemeStructureSheafOn (reducedStructure x).ideal) ≅
      (Scheme.Modules.pushforward (ι (j x))).obj
        ((Scheme.Modules.pushforward (map j x)).obj
          (SheafOfModules.unit (scheme x).ringCatSheaf)))

/- Remark 51.8.5 (3): for an open immersion of locally Noetherian schemes, the
composite pushforward of `𝒪_(scheme x)` is coherent if and only if its pushforward along
the induced map between reduced point closures is coherent. -/
@[stacks 0BK2] #check
  (AlgebraicGeometry.Scheme.PointClosure.pushforwardStructureSheaf_isCoherent_iff j x :
    ((Scheme.Modules.pushforward j).obj
        (closedSubschemeStructureSheafOn (reducedStructure x).ideal)).IsCoherent ↔
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.PointClosure.map j x)).obj
        (SheafOfModules.unit
          (AlgebraicGeometry.Scheme.PointClosure.scheme x).ringCatSheaf)).IsCoherent)

end


end AlgebraicGeometry.Scheme.PointClosure
