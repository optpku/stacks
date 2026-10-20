module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Linear
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor.Associator

/-!
# Composition of Eilenberg--Watts functors

This module owns the composite-kernel functor and the composition law for
Eilenberg--Watts correspondences.
-/

@[expose] public section

open CategoryTheory
open Module.Bimodule

universe u

namespace Module.Bimodule.RelativeTensor

variable {R A B C : Type u} (K K' : Type u)
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [Ring C] [Algebra R C]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]
variable [AddCommGroup K'] [Module R K'] [Module B K'] [Module Cᵐᵒᵖ K']
variable [IsScalarTower R B K'] [IsScalarTower R Cᵐᵒᵖ K']
variable [SMulCommClass B Cᵐᵒᵖ K']

/-- The functor represented by the categorical balanced tensor of composable kernels `K` and `K'`. -/
noncomputable abbrev tensorCompositeFunctor :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ :=
  rightModuleFunctor (R := R) (A := A) ⋙
    CategoryTheory.Bimod.tensorRight
      ((toBimod (R := R) (A := A) (B := B) K).tensorBimod
        (toBimod (R := R) (A := B) (B := C) K')) ⋙
    (@rightModuleEquivalence R C _ _ _).inverse

/-- Sequential tensoring by `K` and `K'` is naturally isomorphic to the composite-kernel functor.

The isomorphism is assembled from canonical comparisons: the categorical/ordinary relative tensor
comparison `Ordinary.categoricalIso` for `K` and `K'`, the counit of the ordinary right
`B`-module equivalence, and the balanced tensor associator `Bimod.tensorRightCompIso`. -/
noncomputable def tensorCompositeFunctorIso :
    tensorModuleFunctor (R := R) (A := A) (B := B) K ⋙
        tensorModuleFunctor (R := R) (A := B) (B := C) K' ≅
      tensorCompositeFunctor (R := R) (A := A) (B := B) (C := C) K K' :=
  -- `tensorModuleFunctor K' ≅ (realize ⋙ tensorRight K') ⋙ extract` on the second factor.
  Functor.isoWhiskerLeft (tensorModuleFunctor (R := R) (A := A) (B := B) K)
      (Functor.isoWhiskerRight
        (Ordinary.categoricalIso (R := R) (A := B) (B := C) K').symm
        (@rightModuleEquivalence R C _ _ _).inverse) ≪≫
    -- Cancel `extract_B ⋙ realize_B` by the counit of the ordinary right-module equivalence.
    Functor.isoWhiskerLeft (Ordinary.functor (R := R) (A := A) (B := B) K)
      (Functor.isoWhiskerRight (@rightModuleEquivalence R B _ _ _).counitIso
          (CategoryTheory.Bimod.tensorRight (toBimod (R := R) (A := B) (B := C) K') ⋙
            (@rightModuleEquivalence R C _ _ _).inverse) ≪≫
        Functor.leftUnitor _) ≪≫
    -- Replace the ordinary tensor by `K` with the categorical balanced tensor.
    Functor.isoWhiskerRight (Ordinary.categoricalIso (R := R) (A := A) (B := B) K).symm
      (CategoryTheory.Bimod.tensorRight (toBimod (R := R) (A := B) (B := C) K') ⋙
        (@rightModuleEquivalence R C _ _ _).inverse) ≪≫
    -- Associativity of balanced tensor products of the kernels.
    Functor.isoWhiskerLeft (rightModuleFunctor (R := R) (A := A))
      (Functor.isoWhiskerRight
        (CategoryTheory.Bimod.tensorRightCompIso
          (toBimod (R := R) (A := A) (B := B) K) (toBimod (R := R) (A := B) (B := C) K'))
        (@rightModuleEquivalence R C _ _ _).inverse)

end Module.Bimodule.RelativeTensor

namespace ModuleCat
namespace EilenbergWatts

variable {R A B C K K' : Type u}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [Ring C] [Algebra R C]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]
variable [AddCommGroup K'] [Module R K'] [Module B K'] [Module Cᵐᵒᵖ K']
variable [IsScalarTower R B K'] [IsScalarTower R Cᵐᵒᵖ K']
variable [SMulCommClass B Cᵐᵒᵖ K']

/-- Given identifications `F ≅ - ⊗_A K` and `F' ≅ - ⊗_B K'`, the composite `F ⋙ F'` is
identified with tensoring by the balanced tensor `K ⊗_B K'`. -/
noncomputable def tensorCompositionIso
    {F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ}
    {F' : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ}
    (e : F ≅ Module.Bimodule.RelativeTensor.tensorModuleFunctor (R := R) (A := A) (B := B) K)
    (e' : F' ≅
      Module.Bimodule.RelativeTensor.tensorModuleFunctor (R := R) (A := B) (B := C) K') :
    F ⋙ F' ≅
      Module.Bimodule.RelativeTensor.tensorCompositeFunctor
        (R := R) (A := A) (B := B) (C := C) K K' :=
  Functor.isoWhiskerRight e F' ≪≫
    Functor.isoWhiskerLeft
      (Module.Bimodule.RelativeTensor.tensorModuleFunctor (R := R) (A := A) (B := B) K) e' ≪≫
    Module.Bimodule.RelativeTensor.tensorCompositeFunctorIso (R := R) K K'

/-- Remark 56.3.4: composable Eilenberg--Watts correspondences compose through the balanced
tensor of kernels.  The isomorphism is `tensorCompositionIso`. -/
theorem tensorComposition
    (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
    (F' : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)
    (hF : Admissible R A B F)
    (hF' : Admissible R B C F')
    (hK : Nonempty (F ≅
      (@Module.Bimodule.RelativeTensor.tensorModuleFunctor R A B K _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)))
    (hK' : Nonempty (F' ≅
      (@Module.Bimodule.RelativeTensor.tensorModuleFunctor R B C K' _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ))) :
    Nonempty (F ⋙ F' ≅
      (@Module.Bimodule.RelativeTensor.tensorCompositeFunctor R A B C K K'
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Cᵐᵒᵖ)) :=
  hK.elim fun e ↦ hK'.elim fun e' ↦ ⟨tensorCompositionIso e e'⟩

end EilenbergWatts
end ModuleCat
