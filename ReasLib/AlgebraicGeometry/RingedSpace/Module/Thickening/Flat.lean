module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealMul.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.Strict
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver

/-!
# Flatness of modules along a strict morphism of first-order thickenings

For a strict morphism of first-order thickenings, an `𝒪_{X'}`-module whose restriction
to `X` is flat over `S` is flat over `S'` if and only if the canonical map
`f^* 𝒥 ⊗ F ⟶ ℐ F'` is an isomorphism, in which case both factor maps are isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom (actionToIdealMulRestrict)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U) (F' : T.right.Modules)

/-- For a strict morphism of first-order thickenings, a module with flat reduction is
flat over the thickened base if and only if its source-ideal action is an isomorphism. -/
theorem isFlatOver_iff_isIso_sourceIdealMulMap
    [SheafOfModules.IsFlatOver ((T.hom^*).obj F') g.left] (hg : IsStrict g) :
    SheafOfModules.IsFlatOver F' g.right ↔ IsIso (sourceIdealMulMap g F') := sorry

/-- For a strict morphism of first-order thickenings, invertibility of the source-ideal
action implies invertibility of the tensor of the source ideal comparison with the reduction. -/
theorem isIso_sourceIdealMap_tensor (hg : IsStrict g)
    [IsIso (sourceIdealMulMap g F')] :
    IsIso (tensorHom (sourceIdealMap g) (𝟙 ((T.hom^*).obj F'))) := sorry

/-- For a strict morphism of first-order thickenings, invertibility of the source-ideal
action implies invertibility of the reduced ideal action. -/
theorem isIso_actionToIdealMulRestrict (hg : IsStrict g)
    [IsIso (sourceIdealMulMap g F')] :
    IsIso (actionToIdealMulRestrict T.hom F') := sorry

/-- The tensor of the source ideal comparison with the reduction is canonically invertible
when the morphism is strict and the source-ideal action is invertible. -/
instance instIsIso_sourceIdealMap_tensor {g : T ⟶ U} {F' : T.right.Modules}
    [Epi (idealMap g)] [IsIso (sourceIdealMulMap g F')] :
    IsIso (tensorHom (sourceIdealMap g) (𝟙 ((T.hom^*).obj F'))) :=
  isIso_sourceIdealMap_tensor g F' (inferInstance : Epi (idealMap g))

/-- Along a strict morphism of first-order thickenings, the source-ideal action on a
module flat over the thickened base is an isomorphism. -/
theorem isIso_sourceIdealMulMap_of_isFlatOver {G' : T.right.Modules}
    [SheafOfModules.IsFlatOver G' g.right] (hg : IsStrict g) :
    IsIso (sourceIdealMulMap g G') := sorry

/-- The source-ideal action is canonically invertible for a module flat over the
thickened base when the ideal comparison map is epic. -/
instance instIsIso_sourceIdealMulMap_of_isFlatOver {g : T ⟶ U} {G' : T.right.Modules}
    [Epi (idealMap g)] [SheafOfModules.IsFlatOver G' g.right] :
    IsIso (sourceIdealMulMap g G') :=
  isIso_sourceIdealMulMap_of_isFlatOver g (inferInstance : Epi (idealMap g))

end AlgebraicGeometry.RingedSpace.Thickening.Hom
