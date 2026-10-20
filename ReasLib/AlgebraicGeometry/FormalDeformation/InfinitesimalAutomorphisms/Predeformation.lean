/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Thin
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Comparison
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pushforward

/-!
# Infinitesimal automorphisms of predeformation categories

Unique residue-fibre isomorphisms canonically identify the infinitesimal
automorphism groups of a predeformation category. These identifications also
compare the group of a residue slice with the group at its base object.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Opposite
open Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

namespace CategoryTheory.Functor

open Chosen

/-- The residue fibre of a predeformation category is a thin quiver. -/
instance instIsThin_residueFiber [IsPredeformationCategory p] :
    Quiver.IsThin (p.Fiber (residue Λ k)) :=
  fun x y ↦ (IsPredeformationCategory.unique_residueHom x y).2

/-- The unique morphism between two specified residue-fibre objects. -/
noncomputable def residueFiberHom [IsPredeformationCategory p]
    (x0 y0 : p.Fiber (residue Λ k)) : x0 ⟶ y0 :=
  Classical.choice (IsPredeformationCategory.unique_residueHom x0 y0).1

/-- There is a unique morphism between any two residue-fibre objects. -/
noncomputable instance instUniqueHom_residueFiber [IsPredeformationCategory p]
    (x0 y0 : p.Fiber (residue Λ k)) : Unique (x0 ⟶ y0) :=
  uniqueOfSubsingleton (residueFiberHom p x0 y0)

/-- The canonical isomorphism between two specified residue-fibre objects. -/
noncomputable def residueFiberIso [IsPredeformationCategory p]
    (x0 y0 : p.Fiber (residue Λ k)) : x0 ≅ y0 :=
  iso_of_both_ways (residueFiberHom p x0 y0) (residueFiberHom p y0 x0)

/-- There is a unique isomorphism between any two residue-fibre objects. -/
noncomputable instance instUniqueIso_residueFiber [IsPredeformationCategory p]
    (x0 y0 : p.Fiber (residue Λ k)) : Unique (x0 ≅ y0) :=
  uniqueOfSubsingleton (residueFiberIso p x0 y0)

/-- The morphism to a specified residue-fibre object obtained by residue pushforward. -/
noncomputable def homToResidueFiberObj [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (y : F) : y ⟶ fiberInclusion.obj x0 :=
  Chosen.pushforwardHom p (toResidue (p.obj y)) (Fiber.ofObj p y) ≫
    fiberInclusion.map
      (residueFiberHom p
        (Chosen.pushforwardObj p (toResidue (p.obj y)) (Fiber.ofObj p y)) x0)

/-- Morphisms to a specified residue-fibre object of a predeformation category are equal. -/
theorem hom_eq_toResidueFiberObj [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {y : F} (f g : y ⟶ fiberInclusion.obj x0) :
    f = g := sorry

/-- A specified residue-fibre object is terminal in the total predeformation category. -/
noncomputable instance instUniqueHom_toResidueFiberObj [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (y : F) :
    Unique (y ⟶ fiberInclusion.obj x0) where
  default := homToResidueFiberObj p x0 y
  uniq := fun φ ↦ hom_eq_toResidueFiberObj p x0 φ (homToResidueFiberObj p x0 y)

/-- Every automorphism of a dual-number pushforward is infinitesimal in a
predeformation category. -/
theorem infinitesimalAutomorphismsAt_eq_top [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ = ⊤ := sorry

/-- The full infinitesimal subgroup is canonically equivalent to the automorphism group
of the specified dual-number pushforward. -/
noncomputable def infinitesimalAutomorphismsAtMulEquivAut [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃* Aut x0' :=
  (MulEquiv.subgroupCongr (infinitesimalAutomorphismsAt_eq_top p x0 x0' φ)).trans
    Subgroup.topEquiv

/-- Unique residue-fibre isomorphisms canonically identify infinitesimal groups. -/
noncomputable def infAutAtCanonicalIso [IsPredeformationCategory p]
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p y0 y0' ψ :=
  infAutAtIso_of_fiberIso p (residueFiberIso p x0 y0) φ ψ

/-- The canonical identification acts by conjugation along the unique vertical
comparison of dual-number pushforwards. -/
theorem infAutAtCanonicalIso_apply [IsPredeformationCategory p]
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (α : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infAutAtCanonicalIso p φ ψ α).val =
      (fiberIso_of_fiberIso p (residueFiberIso p x0 y0) φ ψ).conjAut α.val :=
  infAutAtIso_of_fiberIso_apply p (residueFiberIso p x0 y0) φ ψ α

/-- A chosen object of the nonempty residue fibre of a predeformation category. -/
noncomputable def chosenResidueFiberObj [IsPredeformationCategory p] :
    p.Fiber (residue Λ k) :=
  Classical.choice IsPredeformationCategory.nonempty_residueFiber

/-- Every residue-fibre object is canonically isomorphic to the chosen residue object. -/
theorem chosenResidueFiberObj_uniqueIso [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) :
    Nonempty (chosenResidueFiberObj p ≅ x0) :=
  ⟨residueFiberIso p (chosenResidueFiberObj p) x0⟩

/-- The infinitesimal automorphism group presented by the selected dual-number
pushforward of a chosen residue-fibre object. -/
noncomputable abbrev infinitesimalAutomorphisms [IsPredeformationCategory p] : Type w :=
  Aut (Chosen.pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))

/-- The chosen presentation of the infinitesimal group is the automorphism group
of the selected dual-number pushforward. -/
theorem infinitesimalAutomorphisms_def [IsPredeformationCategory p] :
    infinitesimalAutomorphisms p =
      Aut (Chosen.pushforwardObj p (residueToDualNumber Λ k)
        (chosenResidueFiberObj p)) := rfl

/-- The selected dual-number pushforward of a residue-fibre object as a total-category arrow. -/
noncomputable def chosenDualNumberHom [p.op.IsFibered] (x0 : p.Fiber (residue Λ k)) :
    fiberInclusion.obj x0 ⟶
      fiberInclusion.obj (Chosen.pushforwardObj p (residueToDualNumber Λ k) x0) :=
  Chosen.pushforwardHom p (residueToDualNumber Λ k) x0

/-- The selected dual-number pushforward is strongly cocartesian. -/
instance instIsStronglyCocartesian_chosenDualNumberHom [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    p.IsStronglyCocartesian (residueToDualNumber Λ k) (chosenDualNumberHom p x0) :=
  Chosen.pushforwardHom.isStronglyCocartesian p (residueToDualNumber Λ k) x0

/-- Conjugation along the unique pushforward comparison identifies the chosen
infinitesimal group with the automorphism group at any residue-fibre object. -/
noncomputable def infinitesimalAutomorphismsMulEquiv [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) :
    infinitesimalAutomorphisms p ≃*
      Aut (Chosen.pushforwardObj p (residueToDualNumber Λ k) x0) :=
  (fiberIso_of_fiberIso p (residueFiberIso p (chosenResidueFiberObj p) x0)
      (chosenDualNumberHom p (chosenResidueFiberObj p))
      (chosenDualNumberHom p x0)).conjAut

/-- The comparison of chosen infinitesimal-group presentations acts by conjugation. -/
theorem infinitesimalAutomorphismsMulEquiv_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (α : infinitesimalAutomorphisms p) :
    infinitesimalAutomorphismsMulEquiv p x0 α =
      (fiberIso_of_fiberIso p (residueFiberIso p (chosenResidueFiberObj p) x0)
          (chosenDualNumberHom p (chosenResidueFiberObj p))
          (chosenDualNumberHom p x0)).conjAut α := rfl

/-- The chosen infinitesimal group canonically identifies with the infinitesimal
subgroup at any specified residue object and dual-number pushforward. -/
noncomputable def infinitesimalAutomorphismsEquivAt [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphisms p ≃* infinitesimalAutomorphismsAt p x0 x0' φ :=
  (fiberIso_of_fiberIso p (residueFiberIso p (chosenResidueFiberObj p) x0)
      (chosenDualNumberHom p (chosenResidueFiberObj p)) φ).conjAut.trans
    (infinitesimalAutomorphismsAtMulEquivAut p x0 x0' φ).symm

/-- The chosen infinitesimal-group identification acts by the canonical conjugation. -/
theorem infinitesimalAutomorphismsEquivAt_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α : infinitesimalAutomorphisms p) :
    (infinitesimalAutomorphismsEquivAt p x0 x0' φ α).val =
      (fiberIso_of_fiberIso p (residueFiberIso p (chosenResidueFiberObj p) x0)
          (chosenDualNumberHom p (chosenResidueFiberObj p)) φ).conjAut α := sorry

/-- Forgetting the over-category structure gives a fibre object of the original projection. -/
def sliceFiberObj [IsFibered.InGroupoids p.op] (x0 : p.Fiber (residue Λ k))
    {U : ArtinianLocalAlgCat Λ k} (y : (sliceAt p x0).Fiber U) : p.Fiber U :=
  ⟨y.1.left, y.2⟩

/-- Forgetting a slice-fibre automorphism gives an automorphism in the original fibre. -/
noncomputable def sliceFiberAutForget [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {U : ArtinianLocalAlgCat Λ k}
    (y : (sliceAt p x0).Fiber U) (α : Aut y) : Aut (sliceFiberObj p x0 y) :=
  Fiber.isoMk ((Over.forget (fiberInclusion.obj x0)).mapIso (fiberInclusion.mapIso α)) sorry

/-- Every fibre automorphism lifts to the residue slice because its structure map is unique. -/
noncomputable def sliceFiberAutLift [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {U : ArtinianLocalAlgCat Λ k}
    (y : (sliceAt p x0).Fiber U) (β : Aut (sliceFiberObj p x0 y)) : Aut y :=
  Fiber.isoMk
    (Over.isoMk (fiberInclusion.mapIso β)
      (hom_eq_toResidueFiberObj p x0 ((fiberInclusion.mapIso β).hom ≫ y.1.hom) y.1.hom))
    sorry

/-- Forgetting a lifted fibre automorphism recovers that automorphism. -/
theorem sliceFiberAutForget_lift [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {U : ArtinianLocalAlgCat Λ k}
    (y : (sliceAt p x0).Fiber U) (β : Aut (sliceFiberObj p x0 y)) :
    sliceFiberAutForget p x0 y (sliceFiberAutLift p x0 y β) = β := sorry

/-- Lifting a forgotten slice-fibre automorphism recovers that automorphism. -/
theorem sliceFiberAutLift_forget [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {U : ArtinianLocalAlgCat Λ k}
    (y : (sliceAt p x0).Fiber U) (α : Aut y) :
    sliceFiberAutLift p x0 y (sliceFiberAutForget p x0 y α) = α := sorry

/-- Forgetting slice-fibre automorphisms preserves multiplication. -/
theorem sliceFiberAutForget_mul [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {U : ArtinianLocalAlgCat Λ k}
    (y : (sliceAt p x0).Fiber U) (α β : Aut y) :
    sliceFiberAutForget p x0 y (α * β) =
      sliceFiberAutForget p x0 y α * sliceFiberAutForget p x0 y β := sorry

/-- Forgetting the residue slice gives an equivalence of fibre automorphism groups. -/
noncomputable def sliceFiberAutMulEquiv [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {U : ArtinianLocalAlgCat Λ k}
    (y : (sliceAt p x0).Fiber U) :
    Aut y ≃* Aut (sliceFiberObj p x0 y) where
  toFun := sliceFiberAutForget p x0 y
  invFun := sliceFiberAutLift p x0 y
  left_inv := sliceFiberAutLift_forget p x0 y
  right_inv := sliceFiberAutForget_lift p x0 y
  map_mul' := sliceFiberAutForget_mul p x0 y

/-- The image of the selected dual-number slice pushforward under the forgetful functor. -/
noncomputable def sliceChosenDualNumberHom [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (y0 : (sliceAt p x0).Fiber (residue Λ k)) :
    fiberInclusion.obj (sliceFiberObj p x0 y0) ⟶
      fiberInclusion.obj
        (sliceFiberObj p x0
          (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k) y0)) :=
  (Over.forget (fiberInclusion.obj x0)).map
    (Chosen.pushforwardHom (sliceAt p x0) (residueToDualNumber Λ k) y0)

/-- The selected dual-number slice pushforward forgets to a strongly cocartesian arrow. -/
instance instIsStronglyCocartesian_slicePushforward_forget [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (y0 : (sliceAt p x0).Fiber (residue Λ k)) :
    p.IsStronglyCocartesian (residueToDualNumber Λ k)
      (sliceChosenDualNumberHom p x0 y0) := by
  have unopLift {baseSource baseTarget : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {source target : Fᵒᵖ}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.op.IsHomLift base arrow) :
      p.IsHomLift base.unop arrow.unop := by
    cases certificate
    exact IsHomLift.map _
  have opLift {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : F}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.IsHomLift base arrow) :
      p.op.IsHomLift base.op arrow.op := by
    cases certificate
    exact IsHomLift.map _
  have unopCertificate {baseSource baseTarget : (ArtinianLocalAlgCat Λ k)ᵒᵖ}
      {source target : Fᵒᵖ} {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.op.IsStronglyCartesian base arrow) :
      p.IsStronglyCocartesian base.unop arrow.unop := by
    refine { toIsHomLift := unopLift certificate.toIsHomLift
             universal_property' := ?_ }
    intro destination nextBase nextArrow nextLift
    have oppositeLift : p.op.IsHomLift (nextBase.op ≫ base) nextArrow.op := by
      simpa only [op_comp, Quiver.Hom.op_unop] using opLift nextLift
    obtain ⟨factor, ⟨factorLift, factorization⟩, uniqueness⟩ :=
      @IsStronglyCartesian.universal_property' _ _ _ _ p.op _ _ _ _
        base arrow certificate (op destination) nextBase.op nextArrow.op oppositeLift
    refine ⟨factor.unop, ⟨unopLift factorLift, congrArg Quiver.Hom.unop factorization⟩, ?_⟩
    intro candidate candidateProperty
    apply Quiver.Hom.op_inj
    exact uniqueness candidate.op
      ⟨opLift candidateProperty.1, congrArg Quiver.Hom.op candidateProperty.2⟩
  have changeCertificate {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : F}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.IsStronglyCocartesian (p.map arrow) arrow)
      (lift : p.IsHomLift base arrow) : p.IsStronglyCocartesian base arrow := by
    cases lift
    exact certificate
  let sliceHom := Chosen.pushforwardHom (sliceAt p x0) (residueToDualNumber Λ k) y0
  have sliceLift :=
    (Chosen.pushforwardHom.isStronglyCocartesian
      (sliceAt p x0) (residueToDualNumber Λ k) y0).toIsHomLift
  have forgottenLift : p.IsHomLift (residueToDualNumber Λ k) sliceHom.left :=
    IsHomLift.of_fac' p _ _
      (@IsHomLift.domain_eq _ _ _ _ (sliceAt p x0) _ _ _ _ _ sliceHom sliceLift)
      (@IsHomLift.codomain_eq _ _ _ _ (sliceAt p x0) _ _ _ _ _ sliceHom sliceLift)
      (@IsHomLift.fac' _ _ _ _ (sliceAt p x0) _ _ _ _ _ sliceHom sliceLift)
  exact changeCertificate
    (unopCertificate
      (IsFibered.isStronglyCartesian_of_isCartesian p.op
        (p.op.map sliceHom.left.op) sliceHom.left.op)) forgottenLift

/-- The infinitesimal group of a residue slice canonically identifies with the
infinitesimal subgroup at the base residue object. -/
noncomputable def infinitesimalAutomorphisms_sliceAt [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphisms (sliceAt p x0) ≃*
      infinitesimalAutomorphismsAt p x0 x0' φ :=
  let y0 := chosenResidueFiberObj (sliceAt p x0)
  let comparison :=
    fiberIso_of_fiberIso p (residueFiberIso p (sliceFiberObj p x0 y0) x0)
      (sliceChosenDualNumberHom p x0 y0) φ
  (sliceFiberAutMulEquiv p x0
      (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k) y0)).trans
    (comparison.conjAut.trans (infinitesimalAutomorphismsAtMulEquivAut p x0 x0' φ).symm)

/-- The residue-slice identification forgets slice automorphisms and then conjugates
along the canonical pushforward comparison. -/
theorem infinitesimalAutomorphisms_sliceAt_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α : infinitesimalAutomorphisms (sliceAt p x0)) :
    (infinitesimalAutomorphisms_sliceAt p x0 x0' φ α).val =
      (fiberIso_of_fiberIso p
          (residueFiberIso p
            (sliceFiberObj p x0 (chosenResidueFiberObj (sliceAt p x0))) x0)
          (sliceChosenDualNumberHom p x0 (chosenResidueFiberObj (sliceAt p x0))) φ).conjAut
        (sliceFiberAutMulEquiv p x0
          (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k)
            (chosenResidueFiberObj (sliceAt p x0))) α) := sorry

end CategoryTheory.Functor
