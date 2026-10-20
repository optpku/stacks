/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Symmetric
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Homogeneous components of conormal algebras

The symmetric and total conormal algebras of an immersion have homogeneous module
subobjects. Their canonical comparison preserves these subobjects and restricts to
isomorphisms in degrees zero and one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The degree-`n` subobject of the symmetric conormal algebra is the image of the
sheafification of the sectionwise span of products of exactly `n` generators.
The empty product supplies degree zero. -/
def symmetricDegree (n : ℕ) :
    Subobject (SymmetricAlgebra.underlyingModule (Hom.conormalSheaf i)) := by
  let O := commStructureSheaf Z
  let F := Modules.toComm (Hom.conormalSheaf i)
  let G := fun U : (smallEtaleSite Z)ᵒᵖ ↦
    Submodule.span (O.obj.obj U)
      (Set.range fun x : Fin n → F.val.obj U ↦
        ∏ j, _root_.SymmetricAlgebra.ι (O.obj.obj U) (F.val.obj U) (x j))
  let P : PresheafOfModules.{u} (ringSheaf (smallEtaleTopology Z) O).obj :=
    { obj := fun U ↦ ModuleCat.of (O.obj.obj U) (G U)
      map := fun f ↦ ModuleCat.homMk
        (AddCommGrpCat.ofHom
          { toFun := fun x ↦
              ⟨PresheafOfModules.SymmetricAlgebra.restrictionRingHom O.obj F.val f x.val,
                by sorry⟩
            map_zero' := sorry
            map_add' := sorry })
        (fun _ ↦ sorry)
      map_id := fun _ ↦ sorry
      map_comp := fun _ _ ↦ sorry }
  let A := (restrictionAlong (SymmetricAlgebra.structureMap (Hom.conormalSheaf i))).obj
    (unitModule (smallEtaleTopology Z) (SymmetricAlgebra.sheaf (Hom.conormalSheaf i)))
  let f : P ⟶ A.val :=
    { app := fun U ↦ ModuleCat.homMk
        (AddCommGrpCat.ofHom
          { toFun := fun x ↦
              ((toSheafify (smallEtaleTopology Z)
                (PresheafOfModules.SymmetricAlgebra.commRingPresheaf O.obj F.val)).app U).hom
                  x.val
            map_zero' := sorry
            map_add' := sorry })
        (fun _ ↦ sorry)
      naturality := fun _ ↦ sorry }
  exact imageSubobject
    (Modules.ofCommMap ((moduleSheafificationHomEquiv O P A).symm f))

/-- The degree-`n` subobject of the total conormal algebra is the image of the
pullback of the sheafified degree-`n` coborder associated graded module, mapped
through the canonical associated-graded inclusion. -/
def totalDegree (n : ℕ) : Subobject (Modules.ofComm (totalUnderlyingModule i)) := by
  let O := commStructureSheaf (Hom.coborder i)
  let G := fun U : (smallEtaleSite (Hom.coborder i))ᵒᵖ ↦ coborderGradeSection i n U
  let P : PresheafOfModules.{u} (ringSheaf (smallEtaleTopology (Hom.coborder i)) O).obj :=
    { obj := fun U ↦ ModuleCat.of (O.obj.obj U) (G U)
      map := fun f ↦ ModuleCat.homMk
        (AddCommGrpCat.ofHom
          { toFun := fun x ↦
              Ideal.AssociatedGraded.mapGrade
                (KernelIdeal.sectionIdeal (coborderKernelMap i) _)
                (KernelIdeal.sectionIdeal (coborderKernelMap i) _)
                (O.obj.map f).hom (coborderKernel_sectionIdeal_le_comap i f) n x
            map_zero' := sorry
            map_add' := sorry })
        (fun _ ↦ sorry)
      map_id := fun _ ↦ sorry
      map_comp := fun _ _ ↦ sorry }
  let f : P ⟶ (totalPushforwardUnitModule i).val :=
    { app := fun U ↦ ModuleCat.homMk
        (AddCommGrpCat.ofHom
          { toFun := fun x ↦
              ((InducedCategory.Hom.hom (totalInrAdjunct i)).app U).hom
                (((toSheafify (smallEtaleTopology (Hom.coborder i))
                  (coborderGradePresheaf i)).app U).hom x.val)
            map_zero' := sorry
            map_add' := sorry })
        (fun _ ↦ sorry)
      naturality := fun _ ↦ sorry }
  let M := Modules.ofComm ((moduleSheafification.{u + 1, u, u, u} O).obj P)
  let g : M ⟶ Modules.ofComm (totalPushforwardUnitModule i) :=
    Modules.ofCommMap
      ((moduleSheafificationHomEquiv O P (totalPushforwardUnitModule i)).symm f)
  exact imageSubobject
    (((Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).homEquiv
      M (Modules.ofComm (totalUnderlyingModule i))).symm
        (g ≫ totalPushforwardUnitToPushforward i))

/-- The module morphism underlying the canonical symmetric-to-total comparison. -/
def symmetricToTotalModule :
    SymmetricAlgebra.underlyingModule (Hom.conormalSheaf i) ⟶
      Modules.ofComm (totalUnderlyingModule i) where
  val :=
    { app := fun U ↦ ModuleCat.homMk
        (AddCommGrpCat.ofHom
          { toFun := fun x ↦
              ((InducedCategory.Hom.hom (symmetricToTotal i).hom.right).app U).hom x
            map_zero' := sorry
            map_add' := sorry })
        (fun _ ↦ sorry)
      naturality := fun _ ↦ sorry }

/-- The symmetric homogeneous subobjects internally decompose the symmetric
conormal module, contain the unit in degree zero, and multiply by adding degrees. -/
theorem symmetricDegree_isGrading :
    IsIso (Sigma.desc fun n : ℕ ↦ (symmetricDegree i n).arrow) ∧
      (∀ U : (smallEtaleSite Z)ᵒᵖ,
        ∃ x : (symmetricDegree i 0 : Z.Modules).val.obj U,
          (symmetricDegree i 0).arrow.val.app U x =
            (1 : (SymmetricAlgebra.sheaf (Hom.conormalSheaf i)).obj.obj U)) ∧
      (∀ (n m : ℕ) (U : (smallEtaleSite Z)ᵒᵖ)
        (x : (symmetricDegree i n : Z.Modules).val.obj U)
        (y : (symmetricDegree i m : Z.Modules).val.obj U),
        ∃ z : (symmetricDegree i (n + m) : Z.Modules).val.obj U,
          (symmetricDegree i (n + m)).arrow.val.app U z =
            Mul.mul (α := (SymmetricAlgebra.sheaf (Hom.conormalSheaf i)).obj.obj U)
              ((symmetricDegree i n).arrow.val.app U x)
              ((symmetricDegree i m).arrow.val.app U y)) :=
  sorry

/-- The total homogeneous subobjects internally decompose the total conormal
module, contain the unit in degree zero, and multiply by adding degrees. -/
theorem totalDegree_isGrading :
    IsIso (Sigma.desc fun n : ℕ ↦ (totalDegree i n).arrow) ∧
      (∀ U : (smallEtaleSite Z)ᵒᵖ,
        ∃ x : (totalDegree i 0 : Z.Modules).val.obj U,
          (totalDegree i 0).arrow.val.app U x = (1 : (totalSheaf i).obj.obj U)) ∧
      (∀ (n m : ℕ) (U : (smallEtaleSite Z)ᵒᵖ)
        (x : (totalDegree i n : Z.Modules).val.obj U)
        (y : (totalDegree i m : Z.Modules).val.obj U),
        ∃ z : (totalDegree i (n + m) : Z.Modules).val.obj U,
          (totalDegree i (n + m)).arrow.val.app U z =
            Mul.mul (α := (totalSheaf i).obj.obj U)
              ((totalDegree i n).arrow.val.app U x)
              ((totalDegree i m).arrow.val.app U y)) :=
  sorry

/-- The symmetric-to-total comparison maps every homogeneous symmetric subobject
into the corresponding homogeneous total subobject. -/
theorem symmetricToTotal_preservesDegree (n : ℕ) :
    imageSubobject ((symmetricDegree i n).arrow ≫ symmetricToTotalModule i) ≤
      totalDegree i n :=
  sorry

/-- The canonical comparison restricted to its degree-`n` homogeneous subobjects. -/
def symmetricToTotalDegree (n : ℕ) :
    (symmetricDegree i n : Z.Modules) ⟶ (totalDegree i n : Z.Modules) :=
  factorThruImageSubobject ((symmetricDegree i n).arrow ≫ symmetricToTotalModule i) ≫
    Subobject.ofLE _ _ (symmetricToTotal_preservesDegree i n)

/-- Inclusion of the homogeneous restriction recovers the original comparison
after inclusion of the source homogeneous subobject. -/
theorem symmetricToTotalDegree_arrow (n : ℕ) :
    symmetricToTotalDegree i n ≫ (totalDegree i n).arrow =
      (symmetricDegree i n).arrow ≫ symmetricToTotalModule i :=
  sorry

/-- The degree-zero restriction of the symmetric-to-total comparison is an isomorphism. -/
instance instIsIso_symmetricToTotalDegree_zero : IsIso (symmetricToTotalDegree i 0) :=
  sorry

/-- The degree-one restriction of the symmetric-to-total comparison is an isomorphism. -/
instance instIsIso_symmetricToTotalDegree_one : IsIso (symmetricToTotalDegree i 1) :=
  sorry

/-- Every homogeneous component of the symmetric conormal algebra is quasi-coherent. -/
instance instIsQuasicoherent_symmetricDegree (n : ℕ) :
    (symmetricDegree i n : Z.Modules).IsQuasicoherent :=
  sorry

/-- Every homogeneous component of the total conormal algebra is quasi-coherent. -/
instance instIsQuasicoherent_totalDegree (n : ℕ) :
    (totalDegree i n : Z.Modules).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
