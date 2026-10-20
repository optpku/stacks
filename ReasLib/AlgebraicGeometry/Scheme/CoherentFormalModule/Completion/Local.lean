module

public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Distance
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.AdicCompletion.CompleteModule

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The inverse system of stalk modules of a coherent formal module at a point of `U`. -/
abbrev stalkSystem (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    SequentialInverseSystem (ModuleCat ((S.U.toScheme).presheaf.stalk y)) :=
  F.obj ⋙ (SheafOfModules.isCoherent (S.U.toScheme).ringCatSheaf).ι ⋙
    (S.U.toScheme).toRingedSpace.stalkModuleFunctor y

/-- The defining expression for the inverse system of completed-stalk stages. -/
theorem stalkSystem_def (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    stalkSystem S F y =
      F.obj ⋙ (SheafOfModules.isCoherent (S.U.toScheme).ringCatSheaf).ι ⋙
        (S.U.toScheme).toRingedSpace.stalkModuleFunctor y := sorry

/-- The stalk of a coherent formal module, obtained as the inverse limit of its stage stalks. -/
noncomputable def stalkLimit (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    ModuleCat ((S.U.toScheme).presheaf.stalk y) :=
  limit (stalkSystem S F y)

/-- The inverse-limit description of `stalkLimit`. -/
theorem stalkLimit_def (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    stalkLimit S F y = limit (stalkSystem S F y) := sorry

/-- The canonical map from `A` to the local ring of `U` at `y`. -/
noncomputable def localRingMap (S : AffineAlgebraizationSetup A) (y : S.U) :
    A →+* (S.U.toScheme).presheaf.stalk y :=
  ((S.U.toScheme).presheaf.germ ⊤ y (Set.mem_univ y)).hom.comp
    (Scheme.Hom.sectionsMap S.U.ι ⊤)

/-- The local-ring map is induced by restriction to `U` followed by the germ at `y`. -/
theorem localRingMap_def (S : AffineAlgebraizationSetup A) (y : S.U) :
    localRingMap S y =
      ((S.U.toScheme).presheaf.germ ⊤ y (Set.mem_univ y)).hom.comp
        (Scheme.Hom.sectionsMap S.U.ι ⊤) := sorry

/-- The extension of the defining ideal `S.I` to the stalk of `U` at `y`. -/
noncomputable def stalkIdeal (S : AffineAlgebraizationSetup A) (y : S.U) :
    Ideal ((S.U.toScheme).presheaf.stalk y) :=
  S.I.map (localRingMap S y)

/-- The stalk ideal is the image of `S.I` under the canonical local-ring map. -/
theorem stalkIdeal_def (S : AffineAlgebraizationSetup A) (y : S.U) :
    stalkIdeal S y = S.I.map (localRingMap S y) := sorry

/-- The canonical identification of the local rings on `U` and `X` at `y`, used to compare their `I`-adic completions. -/
noncomputable def openStalkRingEquiv (S : AffineAlgebraizationSetup A) (y : S.U) :
    (S.U.toScheme).presheaf.stalk y ≃+* S.X.presheaf.stalk (S.U.ι y) :=
  (S.U.stalkIso y).commRingCatIsoToRingEquiv

/-- The canonical map from `A` to the ambient stalk of `X` at the image of `y`. -/
noncomputable def ambientLocalRingMap (S : AffineAlgebraizationSetup A) (y : S.U) :
    A →+* S.X.presheaf.stalk (S.U.ι y) :=
  (openStalkRingEquiv S y).toRingHom.comp (localRingMap S y)

/-- The extended ideal is preserved by the canonical comparison of the `U`- and `X`-stalks. -/
theorem openStalkRingEquiv_map_stalkIdeal (S : AffineAlgebraizationSetup A) (y : S.U) :
    (stalkIdeal S y).map (openStalkRingEquiv S y).toRingHom =
      S.I.map (ambientLocalRingMap S y) := sorry

/-- The `I`-adic completed local ring of `U` at `y`. -/
abbrev completedLocalRing (S : AffineAlgebraizationSetup A) (y : S.U) :=
  AdicCompletion (stalkIdeal S y) ((S.U.toScheme).presheaf.stalk y)

/-- The `I`-adic completion description of `completedLocalRing`. -/
theorem completedLocalRing_def (S : AffineAlgebraizationSetup A) (y : S.U) :
    completedLocalRing S y =
      AdicCompletion (stalkIdeal S y) ((S.U.toScheme).presheaf.stalk y) := sorry

/-- The inverse limit of the stage stalks is complete for the extended ideal in the local ring of `U` at `y`. -/
theorem stalkLimit_isAdicComplete (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    IsAdicComplete (stalkIdeal S y) (stalkLimit S F y) := sorry

/-- The completed stalk is the inverse limit of the stage stalks, equipped with its canonical action by the completed local ring. -/
noncomputable def completedStalk (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    ModuleCat (completedLocalRing S y) :=
  @ModuleCat.of (completedLocalRing S y) _ (stalkLimit S F y) _
    (@IsAdicComplete.completedModule
      ((S.U.toScheme).presheaf.stalk y) _ (stalkIdeal S y)
      (stalkLimit S F y) _ _ (stalkLimit_isAdicComplete S F y))

/-- The carrier of `completedStalk` is `stalkLimit`, with the canonical action supplied by its adic completeness. -/
theorem completedStalk_def (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    completedStalk S F y =
      @ModuleCat.of (completedLocalRing S y) _ (stalkLimit S F y) _
        (@IsAdicComplete.completedModule
          ((S.U.toScheme).presheaf.stalk y) _ (stalkIdeal S y)
          (stalkLimit S F y) _ _ (stalkLimit_isAdicComplete S F y)) := sorry

/-- The extension of `S.I` to the completed local ring at `y`. -/
noncomputable def completedIdeal (S : AffineAlgebraizationSetup A) (y : S.U) :
    Ideal (completedLocalRing S y) :=
  (stalkIdeal S y).map
    (algebraMap ((S.U.toScheme).presheaf.stalk y) (completedLocalRing S y))

/-- The completed ideal is obtained by the two successive canonical scalar extensions. -/
theorem completedIdeal_def (S : AffineAlgebraizationSetup A) (y : S.U) :
    completedIdeal S y = (stalkIdeal S y).map
      (algebraMap ((S.U.toScheme).presheaf.stalk y) (completedLocalRing S y)) := sorry

/-- The extension of the stalk maximal ideal to the `I`-adic completed local ring. -/
noncomputable def completedMaximalIdeal (S : AffineAlgebraizationSetup A) (y : S.U) :
    Ideal (completedLocalRing S y) :=
  (IsLocalRing.maximalIdeal ((S.U.toScheme).presheaf.stalk y)).map
    (algebraMap ((S.U.toScheme).presheaf.stalk y) (completedLocalRing S y))

/-- The completed maximal ideal is obtained by extension along the completion map. -/
theorem completedMaximalIdeal_def (S : AffineAlgebraizationSetup A) (y : S.U) :
    completedMaximalIdeal S y =
      (IsLocalRing.maximalIdeal ((S.U.toScheme).presheaf.stalk y)).map
        (algebraMap ((S.U.toScheme).presheaf.stalk y) (completedLocalRing S y)) := sorry

/-- Embed an extended natural number in the extended integers. -/
def enatToEInt (n : ℕ∞) : EInt :=
  (WithTop.map Int.ofNat n : WithTop ℤ)

/-- The value of the canonical embedding from `ℕ∞` to `EInt`. -/
theorem enatToEInt_apply (n : ℕ∞) :
    enatToEInt n = (WithTop.map Int.ofNat n : WithTop ℤ) := sorry

/-- A point of `Y` lying over `U`, regarded as the corresponding point of `U`. -/
def closedFiberOpenPoint (S : AffineAlgebraizationSetup A) (y : S.Y)
    (hy : S.y y ∈ S.U) : S.U :=
  ⟨S.y y, hy⟩

/-- The image in `X` of `closedFiberOpenPoint S y hy` is the original point of `Y`. -/
theorem closedFiberOpenPoint_image (S : AffineAlgebraizationSetup A) (y : S.Y)
    (hy : S.y y ∈ S.U) :
    S.U.ι (closedFiberOpenPoint S y hy) = S.y y := sorry

/-- The closed subset `Z ⊆ Y` cut out by the image of `S.a` in `A ⧸ S.I`. -/
noncomputable def algebraizationClosedSubset (S : AffineAlgebraizationSetup A) : Closeds S.Y :=
  (Scheme.idealSheafDataOfIdealOnSpec
    (S.a.map (Ideal.Quotient.mk S.I))).support

/-- The ideal-sheaf description of the closed subset `Z ⊆ Y`. -/
theorem algebraizationClosedSubset_def (S : AffineAlgebraizationSetup A) :
    algebraizationClosedSubset S =
      (Scheme.idealSheafDataOfIdealOnSpec
        (S.a.map (Ideal.Quotient.mk S.I))).support := sorry

/-- The distance `δ_Z^Y(y)`, computed wholly inside the closed scheme `Y`. -/
noncomputable def algebraizationDistance (S : AffineAlgebraizationSetup A) (y : S.Y) : ℕ∞ :=
  S.Y.distanceTo (algebraizationClosedSubset S) y

/-- Evaluating `algebraizationDistance` gives the distance inside `Y` to `Z`. -/
theorem algebraizationDistance_apply (S : AffineAlgebraizationSetup A) (y : S.Y) :
    algebraizationDistance S y = S.Y.distanceTo (algebraizationClosedSubset S) y := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
