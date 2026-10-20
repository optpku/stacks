/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.GradedAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Functoriality

/-!
# Pullback maps of conormal algebras

A commutative square of scheme morphisms induces degreewise maps on the associated graded
algebras of the kernel ideals.  After sheafification and adjunction these maps assemble into a
canonical homomorphism from the pulled-back conormal algebra.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

universe u

namespace AlgebraicGeometry.Scheme.ConormalAlgebra

variable {Z X Z' X' : Scheme.{u}}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}

/-- The square of underlying morphisms of sheafed spaces associated to a square of schemes. -/
def sheafSquare (sq : CommSq f i i' g) :
    CommSq f.toShHom i.toShHom i'.toShHom g.toShHom :=
  ⟨by
    rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
      ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, sq.w]⟩

/-- The middle structure-sheaf morphism obtained by adjunction from a square of schemes. -/
noncomputable def structureMiddle (sq : CommSq f i i' g) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction
    CommRingCat.{u} f.base).homEquiv _ _)
    ((RingedSpace.Hom.StructureSheaf.compIso f.toShHom i'.toShHom).hom ≫
      (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
        (congrArg (fun k : Z.toSheafedSpace ⟶ X'.toSheafedSpace ↦ k.hom.base)
          (sheafSquare sq).w)).hom.app X'.sheaf ≫
      (RingedSpace.Hom.StructureSheaf.compIso i.toShHom g.toShHom).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} i.base).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm g.toShHom))

/-- The structure-sheaf map into the pushforward along the upper horizontal morphism. -/
noncomputable def structureTarget :
    Z'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Z.sheaf :=
  RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom

/-- The commutative structure-sheaf square controlling maps between the two kernel ideals. -/
noncomputable def conormalStructureSquare (sq : CommSq f i i' g) :=
  RingedSpace.Hom.Conormal.structureSquare (sheafSquare sq)

/-- The semilinear degree map between the associated graded modules of the two kernel ideals. -/
noncomputable def mapGrade (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :
    KernelIdeal.AssociatedGraded.gradeObj
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom) n U ⟶
      (ModuleCat.restrictScalars ((structureMiddle sq).hom.app U).hom).obj
        (KernelIdeal.AssociatedGraded.gradeObj
          (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) n
          ((Opens.map f.base).op.obj U)) :=
  ModuleCat.semilinearMapAddEquiv ((structureMiddle sq).hom.app U).hom _ _
    (Ideal.AssociatedGraded.mapGradeLinear ((structureMiddle sq).hom.app U).hom
      (SheafOfModules.RingedSite.Conormal.InverseImage.ideal_le_comap
        (Opens.map f.base) (structureMiddle sq) structureTarget
          (conormalStructureSquare sq) U) n)

/-- The extension-of-scalars unit used on the target associated graded component. -/
noncomputable def mapExtendUnit (n : ℕ) (U : (Opens Z')ᵒᵖ) :=
  (ModuleCat.extendRestrictScalarsAdj
    ((RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom).hom.app
      ((Opens.map f.base).op.obj U)).hom).unit.app
    (KernelIdeal.AssociatedGraded.gradeObj
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) n
      ((Opens.map f.base).op.obj U))

/-- The lower homogeneous grade after extension to the lower structure sheaf. -/
noncomputable def mapExtendedGrade (n : ℕ) (U : (Opens Z')ᵒᵖ) :=
  (ModuleCat.extendScalars
    ((RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom).hom.app
      ((Opens.map f.base).op.obj U)).hom).obj
    (KernelIdeal.AssociatedGraded.gradeObj
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) n
      ((Opens.map f.base).op.obj U))

/-- The target sheafification unit on a homogeneous associated graded component. -/
noncomputable def mapSheafificationUnit (n : ℕ) (U : (Opens Z')ᵒᵖ) :=
  (moduleSheafificationUnitToVal Z.sheaf
    (KernelIdeal.AssociatedGraded.presheaf.{u, u}
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) n)).app
      ((Opens.map f.base).op.obj U)

/-- Equality of section-ring composites induced by the commutative structure-sheaf square. -/
def conormalRingSquare (sq : CommSq f i i' g) (U : (Opens Z')ᵒᵖ) :=
  congrArg (fun k ↦ (k.hom.app U).hom) (conormalStructureSquare sq).w

/-- The degree map followed by extension of scalars along the lower vertical structure map. -/
noncomputable def mapCoreExtend (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :=
  mapGrade sq n U ≫
    (ModuleCat.restrictScalars ((structureMiddle sq).hom.app U).hom).map
      (mapExtendUnit n U)

/-- Reassociation of the two consecutive restrictions of scalars in the degreewise map. -/
noncomputable def mapCoreReassociate (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :=
  mapCoreExtend sq n U ≫
    (ModuleCat.restrictScalarsComp ((structureMiddle sq).hom.app U).hom
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom).hom.app
        ((Opens.map f.base).op.obj U)).hom).inv.app (mapExtendedGrade n U)

/-- Transport of restricted scalars across the commutative structure-sheaf square. -/
noncomputable def mapCoreTransport (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :=
  mapCoreReassociate sq n U ≫
    (ModuleCat.restrictScalarsCongr (conormalRingSquare sq U)).hom.app
      (mapExtendedGrade n U)

/-- Reassociation with the structure map into the pushforward sheaf. -/
noncomputable def mapCoreTarget (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :=
  mapCoreTransport sq n U ≫
    (ModuleCat.restrictScalarsComp
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom).hom.app U).hom
      (structureTarget.hom.app U).hom).hom.app (mapExtendedGrade n U)

/-- The restricted-scalar composite underlying the degreewise conormal-algebra comparison. -/
noncomputable def mapPresheafCore (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :=
  mapCoreTarget sq n U ≫
    (ModuleCat.restrictScalars
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom).hom.app U).hom).map
      ((ModuleCat.restrictScalars (structureTarget.hom.app U).hom).map
        (mapSheafificationUnit n U))

/-- The map on a homogeneous associated-graded presheaf component induced by a commutative
square of scheme morphisms. -/
noncomputable def mapPresheafApp (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :
    (KernelIdeal.AssociatedGraded.presheaf.{u, u}
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom) n).obj U ⟶
      (((Scheme.Modules.pushforward f).obj ((Scheme.ConormalAlgebra i).obj n)).val.obj U) :=
  ((ModuleCat.extendRestrictScalarsAdj
    ((RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom).hom.app U).hom).homEquiv
      _ _).symm (mapPresheafCore sq n U)

/-- The component construction is the extension-of-scalars transpose of the degreewise
associated-graded map followed by the target sheafification unit. -/
theorem mapPresheafApp_apply (sq : CommSq f i i' g) (n : ℕ)
    (U : (Opens Z')ᵒᵖ) :
    (ModuleCat.extendRestrictScalarsAdj
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom).hom.app U).hom).homEquiv
        _ _ (mapPresheafApp sq n U) = mapPresheafCore sq n U := sorry

/-- The degreewise associated-graded comparison commutes with restriction of open sets. -/
theorem mapPresheafApp_naturality (sq : CommSq f i i' g) (n : ℕ)
    {U V : (Opens Z')ᵒᵖ} (h : U ⟶ V) :
    (KernelIdeal.AssociatedGraded.presheaf.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom) n).map h ≫
      (ModuleCat.restrictScalars (Z'.presheaf.map h).hom).map
        (mapPresheafApp sq n V) =
      mapPresheafApp sq n U ≫
        (((Scheme.Modules.pushforward f).obj ((Scheme.ConormalAlgebra i).obj n)).val.map h) := sorry

/-- The presheaf morphism whose sheafification is adjoint to the degreewise conormal-algebra
comparison. -/
noncomputable def mapPresheaf (sq : CommSq f i i' g) (n : ℕ) :
    KernelIdeal.AssociatedGraded.presheaf.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom) n ⟶
      ((Scheme.Modules.pushforward f).obj ((Scheme.ConormalAlgebra i).obj n)).val where
  app U := mapPresheafApp sq n U
  naturality h := mapPresheafApp_naturality sq n h

/-- The pushforward-side adjoint of the degree-`n` conormal-algebra comparison. -/
noncomputable def mapAdjoint (sq : CommSq f i i' g) (n : ℕ) :
    (Scheme.ConormalAlgebra i').obj n ⟶
      (Scheme.Modules.pushforward f).obj ((Scheme.ConormalAlgebra i).obj n) :=
  (moduleSheafificationHomEquiv Z'.sheaf
    (KernelIdeal.AssociatedGraded.presheaf.{u, u}
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom) n)
    ((Scheme.Modules.pushforward f).obj ((Scheme.ConormalAlgebra i).obj n))).symm
      (mapPresheaf sq n)

/-- The degree-`n` component of the canonical conormal-algebra pullback comparison. -/
noncomputable def mapComponent (sq : CommSq f i i' g) (n : ℕ) :
    (Scheme.Modules.pullback f).obj ((Scheme.ConormalAlgebra i').obj n) ⟶
      (Scheme.ConormalAlgebra i).obj n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (mapAdjoint sq n)

/-- The degree-zero component of the conormal-algebra comparison preserves the unit. -/
theorem map_one (sq : CommSq f i i' g) (U : (Z.Opens)ᵒᵖ) :
    (((mapComponent sq 0).val.app U).hom)
        ((Scheme.Modules.GradedAlgebra.pullback f
          (Scheme.ConormalAlgebra i')).one U) =
      (Scheme.ConormalAlgebra i).one U := sorry

/-- The conormal-algebra comparison preserves multiplication of homogeneous local sections. -/
theorem map_mul (sq : CommSq f i i' g) (U : (Z.Opens)ᵒᵖ) (n m : ℕ)
    (a : ((Scheme.Modules.GradedAlgebra.pullback f
      (Scheme.ConormalAlgebra i')) n).val.obj U)
    (b : ((Scheme.Modules.GradedAlgebra.pullback f
      (Scheme.ConormalAlgebra i')) m).val.obj U) :
    (((mapComponent sq (n + m)).val.app U).hom)
        ((Scheme.Modules.GradedAlgebra.pullback f
          (Scheme.ConormalAlgebra i')).mul U n m a b) =
      (Scheme.ConormalAlgebra i).mul U n m
        ((((mapComponent sq n).val.app U).hom) a)
        ((((mapComponent sq m).val.app U).hom) b) := sorry

/-- The canonical homomorphism from the pullback of one conormal algebra to the other in a
commutative square of schemes. -/
noncomputable def map (sq : CommSq f i i' g) :
    GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i) where
  hom := mapComponent sq
  map_one := map_one sq
  map_mul := map_mul sq

/-- A conormal-algebra homomorphism has the canonical degreewise local formula when every
adjoint component is the sheafification of the associated-graded presheaf map. -/
def IsMap (sq : CommSq f i i' g)
    (tau : GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i)) : Prop :=
  ∀ n : ℕ,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (tau.hom n) =
      mapAdjoint sq n

/-- The canonical conormal-algebra homomorphism has the degreewise associated-graded local
formula. -/
theorem map_isMap (sq : CommSq f i i' g) : IsMap sq (map sq) := sorry

/-- A conormal-algebra homomorphism with the canonical degreewise local formula is the canonical
comparison. -/
theorem eq_map (sq : CommSq f i i' g)
    {tau : GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i)} (h_tau : IsMap sq tau) :
    tau = map sq := sorry

end AlgebraicGeometry.Scheme.ConormalAlgebra

namespace AlgebraicGeometry

variable {Z X Z' X' : Scheme.{u}}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}

/-- On affine charts in a commutative square, the ambient section-ring map carries the kernel
ideal of the upper immersion into the kernel ideal of the lower immersion. -/
theorem immersionAffineConormalIdeal_le_comap
    (sq : CommSq f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    immersionAffineConormalIdeal i' (U' : X'.Opens) ≤
      Ideal.comap ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom)
        (immersionAffineConormalIdeal i (U : X.Opens)) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have eig : i ⁻¹ᵁ (U : X.Opens) ≤ (i ≫ g) ⁻¹ᵁ (U' : X'.Opens) := by
    intro z hz
    exact e hz
  have efg : i ⁻¹ᵁ (U : X.Opens) ≤ (f ≫ i') ⁻¹ᵁ (U' : X'.Opens) := by
    intro z hz
    change (f ≫ i').base z ∈ (U' : X'.Opens)
    rw [sq.w]
    exact e hz
  have happ :
      i'.app (U' : X'.Opens) ≫
          f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens)) efg =
        g.appLE (U' : X'.Opens) (U : X.Opens) e ≫
          i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl := by
    calc
      i'.app (U' : X'.Opens) ≫
          f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens)) efg =
        (f ≫ i').appLE (U' : X'.Opens) (i ⁻¹ᵁ (U : X.Opens)) efg := by
          symm
          simpa using Scheme.Hom.comp_appLE f i' (U' : X'.Opens)
            (i ⁻¹ᵁ (U : X.Opens)) efg
      _ = (i ≫ g).appLE (U' : X'.Opens) (i ⁻¹ᵁ (U : X.Opens)) eig := by
        simpa [sq.w]
      _ = g.appLE (U' : X'.Opens) (U : X.Opens) e ≫
          i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl := by
        simpa using (Scheme.Hom.appLE_comp_appLE i g (U' : X'.Opens)
          (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) e le_rfl).symm
  have happx := congrArg (fun phi ↦ phi.hom x) happ
  have hzero :
      (f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens)) efg).hom
          ((i'.app (U' : X'.Opens)).hom x) = 0 := by
    simpa [hx]
  have hrewrite :
      (i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl).hom
          ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom x) =
        (f.appLE (i' ⁻¹ᵁ (U' : X'.Opens)) (i ⁻¹ᵁ (U : X.Opens)) efg).hom
          ((i'.app (U' : X'.Opens)).hom x) := by
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using happx.symm
  have hfinal :
      (i.appLE (U : X.Opens) (i ⁻¹ᵁ (U : X.Opens)) le_rfl).hom
          ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom x) = 0 :=
    hrewrite.trans hzero
  simpa [Scheme.Hom.appLE_eq_app] using hfinal

/-- The associated-graded ring map on affine charts induced by the ambient section-ring map. -/
noncomputable abbrev immersionAffineConormalAlgebraMap
    (sq : CommSq f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    immersionAffineConormalAlgebra i' (U' : X'.Opens) →+*
      immersionAffineConormalAlgebra i (U : X.Opens) :=
  Ideal.AssociatedGraded.map
    ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom)
    (immersionAffineConormalIdeal_le_comap sq U U' e)

/-- The affine conormal-algebra comparison is the associated-graded map of the ambient
section-ring homomorphism. -/
theorem immersionAffineConormalAlgebraMap_def
    (sq : CommSq f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    immersionAffineConormalAlgebraMap sq U U' e =
      Ideal.AssociatedGraded.map
        ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom)
        (immersionAffineConormalIdeal_le_comap sq U U' e) := rfl

end AlgebraicGeometry
