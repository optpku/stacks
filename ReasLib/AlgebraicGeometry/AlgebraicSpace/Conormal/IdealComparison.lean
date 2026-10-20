/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.ClosedMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-!
# Comparison of the conormal sheaf with the restricted ideal sheaf

For an immersion of algebraic spaces, the coborder projection `I ⟶ I/I²` pulls
back to a morphism into the conormal sheaf. For a closed immersion this
assembles with the coborder factorization to a comparison
`(Modules.pullback i).obj (Hom.idealSheaf i) ⟶ Hom.conormalSheaf i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.Conormal

variable {S : Scheme.{u}}

/-- The coborder comparison `I ⟶ I/I²`, pulled back along the coborder closed
immersion of an immersion of algebraic spaces. -/
noncomputable def coborderIdealComparison {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsImmersion i] :
    (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (idealSheaf (IsImmersion.liftCoborder i)) ⟶
      conormalSheaf i :=
  (Modules.pullback (IsImmersion.liftCoborder i)).map
    (Modules.quotientByIdeal.π (idealSheafSubobject (IsImmersion.liftCoborder i))
      (idealSheaf (IsImmersion.liftCoborder i)))

/-- `coborderIdealComparison` is pullback of the coborder ideal-quotient
projection. -/
theorem coborderIdealComparison_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsImmersion i] :
    coborderIdealComparison i =
      (Modules.pullback (IsImmersion.liftCoborder i)).map
        (Modules.quotientByIdeal.π (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i))) :=
  rfl

/-- The comparison from the restricted ideal sheaf of a closed immersion to its
conormal sheaf, obtained from the coborder factorization, `Modules.pullbackCompIso`,
`pulledIdealToIdeal`, and `coborderIdealComparison`. -/
noncomputable def pullbackIdealComparison {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (Modules.pullback i).obj (idealSheaf i) ⟶ conormalSheaf i :=
  (eqToIso (congrArg (fun f : Z ⟶ X ↦ Modules.pullback f)
        (IsImmersion.liftCoborder_comp i))).inv.app (idealSheaf i) ≫
    (Modules.pullbackCompIso (IsImmersion.liftCoborder i)
        (IsImmersion.coborderRange i).ι).inv.app (idealSheaf i) ≫
    (Modules.pullback (IsImmersion.liftCoborder i)).map
      (pulledIdealToIdeal
        (⟨(Category.id_comp i).trans (IsImmersion.liftCoborder_comp i).symm⟩ :
          CommSq (𝟙 Z) (IsImmersion.liftCoborder i) i
            (IsImmersion.coborderRange i).ι)) ≫
    coborderIdealComparison i

/-- `pullbackIdealComparison` is the coborder-factorization composite of the
restricted ideal sheaf into the conormal sheaf. -/
theorem pullbackIdealComparison_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    pullbackIdealComparison i =
      (eqToIso (congrArg (fun f : Z ⟶ X ↦ Modules.pullback f)
            (IsImmersion.liftCoborder_comp i))).inv.app (idealSheaf i) ≫
        (Modules.pullbackCompIso (IsImmersion.liftCoborder i)
            (IsImmersion.coborderRange i).ι).inv.app (idealSheaf i) ≫
        (Modules.pullback (IsImmersion.liftCoborder i)).map
          (pulledIdealToIdeal
            (⟨(Category.id_comp i).trans (IsImmersion.liftCoborder_comp i).symm⟩ :
              CommSq (𝟙 Z) (IsImmersion.liftCoborder i) i
                (IsImmersion.coborderRange i).ι)) ≫
        coborderIdealComparison i :=
  rfl

end Hom.Conormal

end AlgebraicGeometry.AlgebraicSpace
