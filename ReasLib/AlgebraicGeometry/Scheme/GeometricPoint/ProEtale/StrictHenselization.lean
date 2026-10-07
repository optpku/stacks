module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ProEtale
public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing

/-!
# Strict henselization as a pro-étale neighbourhood

The spectrum of the étale local ring `𝒪_{S, s̄}^{sh}` is an object of the small
pro-étale site, and evaluation of sheaves there recovers the geometric stalk.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- The structure morphism of the strict henselization scheme at a geometric
point is weakly étale. -/
theorem strictHenselizationMap_weaklyEtale (s : GeometricPoint S) :
    WeaklyEtale (strictHenselizationMap S s (etaleLocalRing S s)) :=
  sorry

/-- The spectrum of `𝒪_{S, s̄}^{sh}` as an object of the small pro-étale site of
`S`. -/
def strictHenselization (s : GeometricPoint S) : S.ProEt :=
  MorphismProperty.Over.mk _ (strictHenselizationMap S s (etaleLocalRing S s))
    (strictHenselizationMap_weaklyEtale s)

/-- The structure morphism of `strictHenselization s` is the canonical map from
the strict henselization scheme. -/
theorem strictHenselization_hom (s : GeometricPoint S) :
    (strictHenselization s).hom =
      strictHenselizationMap S s (etaleLocalRing S s) :=
  sorry

/-- The left scheme of `strictHenselization s` is the spectrum of the étale
local ring. -/
theorem strictHenselization_left (s : GeometricPoint S) :
    (strictHenselization s).left =
      strictHenselizationScheme S s (etaleLocalRing S s) :=
  sorry

/-- Evaluation of a section of the étale structure sheaf at a pointed étale
neighbourhood of `s`, as a map to the coefficient field. -/
def strictHenselizationEvalApp (s : GeometricPoint S)
    (U : ((toSmallEtalePoint s).fiber.Elements)ᵒᵖ) :
    ((CategoryOfElements.π (toSmallEtalePoint s).fiber).op ⋙
      (Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat).obj U ⟶
      RingCat.of s.K :=
  (forget₂ CommRingCat RingCat).map
    (U.unop.2.left.appTop ≫ (Scheme.ΓSpecIso (.of s.K)).hom)

/-- The canonical ring homomorphism `𝒪_{S, s̄}^{sh} → k` obtained by evaluating
étale germs at the geometric point. -/
def strictHenselizationEval (s : GeometricPoint S) :
    etaleLocalRing S s →+* s.K :=
  RingCat.Hom.hom <|
    colimit.desc
      ((CategoryOfElements.π (toSmallEtalePoint s).fiber).op ⋙
        (Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)
      { pt := RingCat.of s.K
        ι :=
          { app := fun U => strictHenselizationEvalApp s U
            naturality := sorry } }

/-- The evaluation map on the étale local ring is assembled from the
neighbourhood-wise evaluations. -/
theorem strictHenselizationEval_app (s : GeometricPoint S)
    (U : ((toSmallEtalePoint s).fiber.Elements)ᵒᵖ) :
    (strictHenselizationEval s).comp
      (RingCat.Hom.hom
        (colimit.ι
          ((CategoryOfElements.π (toSmallEtalePoint s).fiber).op ⋙
            (Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat) U)) =
      RingCat.Hom.hom (strictHenselizationEvalApp s U) :=
  sorry

/-- The canonical lift of a geometric point through the spectrum of
`𝒪_{S, s̄}^{sh}`. -/
def strictHenselizationLift (s : GeometricPoint S) :
    Spec (.of s.K) ⟶ (strictHenselization s).left :=
  Spec.map (CommRingCat.ofHom (strictHenselizationEval s))

/-- The canonical lift is a morphism over `S`. -/
theorem strictHenselizationLift_fac (s : GeometricPoint S) :
    strictHenselizationLift s ≫ (strictHenselization s).hom = s.hom :=
  sorry

/-- The fibre element exhibiting `Spec(𝒪_{S, s̄}^{sh})` as a pro-étale
neighbourhood of `s`. -/
def strictHenselizationFibre (s : GeometricPoint S) :
    (toSmallProetalePoint s).fiber.obj (strictHenselization s) :=
  Over.homMk (strictHenselizationLift s) (strictHenselizationLift_fac s)

/-- The pro-étale neighbourhood corresponding to the strict henselization. -/
def strictHenselizationNeighbourhood (s : GeometricPoint S) :
    ProetaleNeighborhood s :=
  ProetaleNeighborhood.of (strictHenselization s) (strictHenselizationLift s)
    (strictHenselizationLift_fac s)

/-- The fibre element of the strict henselization is the over-morphism of the
canonical lift. -/
theorem strictHenselizationFibre_eq_homMk (s : GeometricPoint S) :
    strictHenselizationFibre s =
      Over.homMk (strictHenselizationLift s) (strictHenselizationLift_fac s) :=
  sorry

/-- The chosen lift of the strict-henselization neighbourhood is the canonical
lift of the geometric point. -/
theorem strictHenselizationNeighbourhood_lift (s : GeometricPoint S) :
    (strictHenselizationNeighbourhood s).lift = strictHenselizationLift s :=
  sorry

/-- The canonical comparison from evaluation at `Spec(𝒪_{S, s̄}^{sh})` to the
presheaf fibre of the associated pro-étale point. -/
def toStalkNatTrans (s : GeometricPoint S) :
    (CategoryTheory.evaluation S.ProEtᵒᵖ (Type u)).obj (op (strictHenselization s)) ⟶
      (toSmallProetalePoint s).presheafFiber :=
  (toSmallProetalePoint s).toPresheafFiberNatTrans
    (strictHenselization s) (strictHenselizationFibre s)

/-- Evaluation of presheaves at `Spec(𝒪_{S, s̄}^{sh})` is canonically isomorphic
to the geometric pro-étale stalk, functorially in the presheaf. -/
theorem toPresheafFiberNatTrans_isIso (s : GeometricPoint S) :
    IsIso (toStalkNatTrans s) :=
  sorry

/-- The component of the canonical comparison at a presheaf `F` is the colimit
cocone leg from sections over the strict henselization. -/
theorem toStalkNatTrans_app (s : GeometricPoint S) (F : S.ProEtᵒᵖ ⥤ Type u) :
    (toStalkNatTrans s).app F =
      (toSmallProetalePoint s).toPresheafFiber (strictHenselization s)
        (strictHenselizationFibre s) F :=
  sorry

/-- Evaluation of sheaves on the small pro-étale site at
`Spec(𝒪_{S, s̄}^{sh})` is canonically isomorphic to the geometric stalk,
functorially in the sheaf. -/
theorem sheafToPresheaf_toPresheafFiberNatTrans_isIso (s : GeometricPoint S) :
    IsIso
      (Functor.whiskerLeft (sheafToPresheaf (ProEt.topology S) (Type u))
        (toStalkNatTrans s)) :=
  sorry

end AlgebraicGeometry.Scheme.GeometricPoint
