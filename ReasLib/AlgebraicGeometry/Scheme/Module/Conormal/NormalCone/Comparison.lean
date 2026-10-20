/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Symmetric
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone

/-!
# The normal cone as a subscheme of the normal bundle

The canonical morphism from the symmetric algebra of the conormal sheaf to the total
conormal algebra induces a morphism from the normal cone to the normal bundle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}}

/-- The canonical morphism from the normal cone of an immersion to its normal bundle. -/
noncomputable def normalConeToNormalBundle (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
    [IsRelativeSpectrumOver Q] :
    normalCone i P ⟶ normalBundle i Q :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := Q)).representableBy.homEquiv.symm
    (⟨normalConeπ i P,
      (QcAlgebraUnder.forget Z).map (ConormalAlgebra.symmetricToTotal i) ≫
        relativeSpecUniversalFamily P⟩ :
      relativeSpectrumPair (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i))
        (normalCone i P))

/-- Pulling back the universal point of the normal bundle along the canonical comparison
morphism gives the normal-cone point induced by the symmetric-to-total algebra map. -/
theorem normalConeToNormalBundle_spec (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
    [IsRelativeSpectrumOver Q] :
    relativeSpectrumPairPullbackMap
        (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i))
        (normalConeToNormalBundle i P Q) (relativeSpecPoint Q) =
      (⟨normalConeπ i P,
        (QcAlgebraUnder.forget Z).map (ConormalAlgebra.symmetricToTotal i) ≫
          relativeSpecUniversalFamily P⟩ :
        relativeSpectrumPair (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i))
          (normalCone i P)) := sorry

/-- The canonical morphism from the normal cone to the normal bundle lies over the source of
the immersion. -/
theorem normalConeToNormalBundle_over (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
    [IsRelativeSpectrumOver Q] :
    normalConeToNormalBundle i P Q ≫ normalBundleπ i Q = normalConeπ i P := sorry

end AlgebraicGeometry.Scheme
