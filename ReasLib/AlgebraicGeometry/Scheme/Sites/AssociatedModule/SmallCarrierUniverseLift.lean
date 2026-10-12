/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard

/-!
# Carrier universe lifts of associated modules on small sites

This module lifts the module carriers of associated modules on the canonical
small Zariski and étale sites while leaving their coefficient sheaves unchanged.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The objectwise universe lift of the presheaf underlying a small associated module. -/
noncomputable def smallCarrierUniverseLiftPresheaf
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    _root_.PresheafOfModules.{u + 1} (smallStructureSheaf σ S).obj where
  obj U := (ModuleCat.uliftFunctor.{u + 1} _).obj ((small σ S F).val.obj U)
  map g := (ModuleCat.uliftFunctor.{u + 1} _).map ((small σ S F).val.map g)
  map_id := sorry
  map_comp := sorry

/-- The carrier-lifted small associated presheaf is objectwise the canonical
module universe lift. -/
theorem smallCarrierUniverseLiftPresheaf_obj
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] (U : (σ.site S)ᵒᵖ) :
    (smallCarrierUniverseLiftPresheaf σ S F).obj U =
      (ModuleCat.uliftFunctor.{u + 1} _).obj ((small σ S F).val.obj U) := sorry

/-- The objectwise carrier lift of a small associated module remains a sheaf. -/
theorem smallCarrierUniverseLiftPresheaf_isSheaf
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (σ.topology S)
      (smallCarrierUniverseLiftPresheaf σ S F).presheaf := sorry

/-- The small associated module with its module carriers lifted by one universe. -/
noncomputable def smallCarrierUniverseLift
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.{u + 1} (smallStructureSheaf σ S) :=
  ⟨smallCarrierUniverseLiftPresheaf σ S F,
    smallCarrierUniverseLiftPresheaf_isSheaf σ S F⟩

/-- The presheaf underlying the carrier-lifted small associated module is its
objectwise carrier lift. -/
theorem smallCarrierUniverseLift_val
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (smallCarrierUniverseLift σ S F).val =
      smallCarrierUniverseLiftPresheaf σ S F := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
