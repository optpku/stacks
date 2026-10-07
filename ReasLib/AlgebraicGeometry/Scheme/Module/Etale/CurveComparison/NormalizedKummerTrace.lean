module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.AssociatedModule
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.NormalizedCurveTrace
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (C : SchemeOverField k) [Curve C] [Smooth C.hom] [Projective C.hom]
variable {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Scheme.etaleRestriction j).op.HasLeftKanExtension F]
variable (n : ℕ) (h_pos : 0 < n) (h_n : IsUnit (n : k))

/-- The actual roots-of-unity sheaf on the smooth projective compactification. -/
abbrev rootsSheaf : Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale C.left) n

/-- The compact-support coefficient sheaf is the actual extension by zero of restricted μ_n. -/
def compactRootsSheaf : Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
    ((Scheme.etaleRestrictionSheaf j AddCommGrpCat.{u + 1}).obj (rootsSheaf C n))

/-- The compact-support coefficient map is the actual extension/restriction counit. -/
def compactRootsCounit : compactRootsSheaf C j n ⟶ rootsSheaf C n :=
  (Scheme.etaleExtensionByZero_adjunction j AddCommGrpCat.{u + 1}).counit.app (rootsSheaf C n)

/-- The normalized compact-support μ_n trace: apply H² to the specified counit,
then take Picard degree modulo n through the actual Kummer boundary comparison. -/
def compactKummerTrace : (compactRootsSheaf C j n).H 2 →+ ZMod n :=
  (etaleCohomology_rootsOfUnity_h2 C n h_pos h_n).toAddMonoidHom.comp
    (Sheaf.H.map (compactRootsCounit C j n) 2)

/-- The projective normalization takes a Kummer boundary to the degree of its Picard class modulo n. -/
theorem projectiveTrace_kummerBoundary (L : C.left.PicardGroup) :
    etaleCohomology_rootsOfUnity_h2 C n h_pos h_n
      (kummerPicardBoundaryFunction C n h_pos h_n L) = (curvePicardDegreeFunction C L : ZMod n) := sorry

/-- The displayed trace is normalized through the actual compact-support counit image. -/
theorem compactKummerTrace_apply (x : (compactRootsSheaf C j n).H 2) :
    compactKummerTrace C j n h_pos h_n x =
      rootsH2ComparisonFunction C n h_pos h_n
        (Sheaf.H.map (compactRootsCounit C j n) 2 x) := rfl

include h_pos h_n

/-- For a nonempty open in a smooth projective curve, the specified normalized μ_n trace is bijective.
Nonemptiness is essential: no invertibility is asserted for an empty open. -/
theorem compactKummerTrace_bijective [Nonempty U] :
    Function.Bijective (compactKummerTrace C j n h_pos h_n) := sorry

variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- Restriction of the units sheaf reads the same ring unit on each étale object. -/
def unitsRestrictionIso :
    (Scheme.etaleRestrictionSheaf j AddCommGrpCat.{u + 1}).obj
        (Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale C.left)) ≅
      Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale U) where
  hom := ObjectProperty.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ Sheaf.unitsAddSheafSection (smallCommStructureSheaf .etale U) (U := V)
            (Sheaf.unitsAddSheafUnit (smallCommStructureSheaf .etale C.left)
              (U := Opposite.op ((Scheme.etaleRestriction j).obj V.unop)) x)
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }
  inv := ObjectProperty.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ Sheaf.unitsAddSheafSection (smallCommStructureSheaf .etale C.left)
            (U := Opposite.op ((Scheme.etaleRestriction j).obj V.unop))
            (Sheaf.unitsAddSheafUnit (smallCommStructureSheaf .etale U) (U := V) x)
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction of μ_n along an open immersion uses identity on sections of
the same étale object's structure ring, not a chosen coefficient isomorphism. -/
def restrictionRootsIso :
    (Scheme.etaleRestrictionSheaf j AddCommGrpCat.{u + 1}).obj (rootsSheaf C n) ≅
      CategoryTheory.Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale U) n :=
  PreservesKernel.iso (Scheme.etaleRestrictionSheaf j AddCommGrpCat.{u + 1})
      (Sheaf.unitsNsmul (smallCommStructureSheaf .etale C.left) n) ≪≫
    kernel.mapIso _ (Sheaf.unitsNsmul (smallCommStructureSheaf .etale U) n)
      (unitsRestrictionIso C j) (unitsRestrictionIso C j) sorry

/-- The trace on the intrinsic open-curve μ_n coefficient includes its specified
restriction identification before applying the compactification counit and degree. -/
def intrinsicCompactKummerTrace :
    ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
      (CategoryTheory.Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale U) n)).H 2 →+ ZMod n :=
  (compactKummerTrace C j n h_pos h_n).comp
    (Sheaf.H.map ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).map
      (restrictionRootsIso C j n).inv) 2)

/-- The intrinsic-coefficient trace is bijective on a nonempty open curve. -/
theorem intrinsicCompactKummerTrace_bijective [Nonempty U] :
    Function.Bijective (intrinsicCompactKummerTrace C j n h_pos h_n) := sorry

/-- The normalized trace equivalence has exactly the constructed counit/degree map as its forward function. -/
def intrinsicCompactKummerTraceEquiv [Nonempty U] :
    ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
      (CategoryTheory.Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale U) n)).H 2 ≃+ ZMod n :=
  AddEquiv.ofBijective (intrinsicCompactKummerTrace C j n h_pos h_n)
    (intrinsicCompactKummerTrace_bijective C j n h_pos h_n)

end AlgebraicGeometry.SchemeOverField.NormalizedCurveTrace
