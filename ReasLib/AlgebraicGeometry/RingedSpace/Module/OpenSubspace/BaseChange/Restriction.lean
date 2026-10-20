/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! Literal restriction of modules over the intrinsic structure sheaf. -/
@[expose] public section
open CategoryTheory TopologicalSpace Topology Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
noncomputable section
universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange

/-- Restriction evaluated on the image open, over the intrinsic restricted ring.
The scalar map is the identity, not an isomorphism chosen from existence. -/
def literalRestriction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    X.Modules ⥤ RingedSpace.Modules (X.restrict U.isOpenEmbedding) := by
  -- Local instance justification (defeq pin): Specialize the proved open-embedding continuity to the intrinsic restricted-space topology required by module pushforward.
  letI : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
    Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  exact SheafOfModules.pushforward (F := U.isOpenEmbedding.functor)
    (R := X.ringCatSheaf)
    (𝟙 (RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)))

/-- The actual module of sections on an image open is the restricted value. -/
theorem literalRestriction_obj (X : RingedSpace.{u}) (U : Opens X.carrier)
    (M : X.Modules) (W : Opens (X.restrict U.isOpenEmbedding).carrier) :
    ((literalRestriction X U).obj M).val.obj (op W) =
      M.val.obj (op (U.isOpenEmbedding.functor.obj W)) := rfl

/-- The scalar action is precisely that of the intrinsic restricted structure ring. -/
theorem literalRestriction_smul (X : RingedSpace.{u}) (U : Opens X.carrier)
    (M : X.Modules) (W : Opens (X.restrict U.isOpenEmbedding).carrier)
    (r : (RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).obj.obj (op W))
    (m : ((literalRestriction X U).obj M).val.obj (op W)) :
    r • m = (r • m : M.val.obj (op (U.isOpenEmbedding.functor.obj W))) := rfl

/-- Scalar compatibility with the opens adjunction counit is the actual
definition of the intrinsic open-immersion structure map. -/
theorem literalScalar_counit (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
        X.ringCatSheaf.obj =
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)).hom ≫
        (Opens.map U.inclusion').op.whiskerLeft
          (𝟙 ((RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).obj)) := by
  apply NatTrans.ext
  funext W
  rfl

/-- The second scalar coherence is the genuine opens-adjunction triangle. -/
theorem literalScalar_unit (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (𝟙 ((RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).obj)) ≫
        U.isOpenEmbedding.functor.op.whiskerLeft
          (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)).hom ≫
        Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.unit)
          (RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).obj =
      𝟙 ((RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).obj) := by
  apply NatTrans.ext
  funext W
  change X.ringCatSheaf.obj.map
      (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
        (U.isOpenEmbedding.functor.obj W.unop)).op ≫
      X.ringCatSheaf.obj.map
        (U.isOpenEmbedding.functor.map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W.unop)).op = 𝟙 _
  calc
    _ = X.ringCatSheaf.obj.map
        ((U.isOpenEmbedding.functor.map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W.unop) ≫
            U.isOpenEmbedding.isOpenMap.adjunction.counit.app
              (U.isOpenEmbedding.functor.obj W.unop)).op) :=
      (X.ringCatSheaf.obj.map_comp _ _).symm
    _ = X.ringCatSheaf.obj.map (𝟙 _) :=
      congrArg (fun k => X.ringCatSheaf.obj.map k.op)
        (U.isOpenEmbedding.isOpenMap.adjunction.left_triangle_components W.unop)
    _ = 𝟙 _ := X.ringCatSheaf.obj.map_id _

/-- Literal restriction and the intrinsic open pushforward are adjoint using
their actual section maps and the proved scalar coherences. -/
def literalAdjunction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    literalRestriction X U ⊣ RingedSpace.Hom.pushforward (X.ofRestrict U.isOpenEmbedding) := by
  -- Local instance justification (proof-local temporary data): Supply the proved continuity certificate to the explicit opens-adjunction construction on module sheaves.
  letI : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
    Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  exact @SheafOfModules.pushforwardPushforwardAdj _ _ _ _
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
    (Opens.grothendieckTopology X.carrier)
    U.isOpenEmbedding.functor (Opens.map U.inclusion')
    (RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)) X.ringCatSheaf
    (Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding) inferInstance
    U.isOpenEmbedding.isOpenMap.adjunction
    (𝟙 (RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)))
    (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding))
    (literalScalar_counit X U) (literalScalar_unit X U)

/-- The concrete literal model is identified with the existing module pullback
by the two explicitly supplied adjunctions. -/
def restrictionBridge (X : RingedSpace.{u}) (U : Opens X.carrier) :
    literalRestriction X U ≅ moduleRestrictionToOpen X U :=
  Adjunction.leftAdjointUniq (literalAdjunction X U)
    (RingedSpace.Hom.pullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding))

end AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange
