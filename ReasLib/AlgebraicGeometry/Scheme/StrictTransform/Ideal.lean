module

public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The ideal sheaf on the blown-up scheme cutting out the scheme-theoretic image of a closed
subscheme's canonical strict transform. -/
noncomputable def strictTransformIdeal
    {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (Y : X.IdealSheafData) : X'.IdealSheafData :=
  (AlgebraicGeometry.strictTransformSnd b (I.comap b) Y.subschemeι).ker

/-- The strict-transform ideal is the kernel ideal of the canonical map to the blown-up
scheme. -/
theorem strictTransformIdeal_def
    {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (Y : X.IdealSheafData) :
    strictTransformIdeal I b Y =
      (AlgebraicGeometry.strictTransformSnd b (I.comap b) Y.subschemeι).ker := sorry

/-- The support of the strict-transform ideal is the closure of the image of the canonical
strict-transform map to the blown-up scheme. -/
theorem strictTransformIdeal_support
    {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (Y : X.IdealSheafData) :
    (strictTransformIdeal I b Y).support =
      TopologicalSpace.Closeds.closure
        (Set.range (AlgebraicGeometry.strictTransformSnd b (I.comap b) Y.subschemeι)) := sorry

end AlgebraicGeometry.IsBlowup
