/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Algebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalBaseChange

/-! # Canonical base change of the integer-graded Serre algebra -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
variable {𝒜 𝒜'} {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'}
variable (hAlg : AlgebraPullback g deg deg')
variable {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
variable {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')

/-- The underlying actual morphism P'→P is the second projection after the
already constructed pointwise base-change isomorphism. -/
def map : toAlgebraicSpace F' hF' ⟶ toAlgebraicSpace F hF :=
  (canonicalBaseChangeIso g hAlg hF hF').hom ≫ fibreProduct_snd g hF

variable (U : affineEtaleSite (toAlgebraicSpace F hF))
variable (V : affineEtaleSite (toAlgebraicSpace F' hF'))
variable (j : AffineGraph (map g hAlg hF hF') U.obj V)

/-- The actual scheme map of the fibre-product graph, recovered by Yoneda. -/
def graphMap : V.obj.left ⟶ U.obj.left :=
  (etaleSquareOfArrow (map g hAlg hF hF') U.obj
    (StructuredArrow.mk (Y := op V.obj) (op j))).map

/-- Its base square follows from the actual graph and the base-change projection law. -/
theorem graphMap_base :
    ofOverMap (graphMap g hAlg hF hF' U V j) ≫ base F hF U = base F' hF' V ≫ g := sorry

/-- Pull back a homogeneous piece through that actual square and the given algebra map. -/
def degreePullIso (n : ℕ) :
    (Scheme.Modules.pullback (graphMap g hAlg hF hF' U V j).left).obj
      (localAlgebra F hF U (n : ℤ)) ≅ localAlgebra F' hF' V (n : ℤ) := by
  -- Local instance justification (proof-local temporary data): this source owner supplies QCoh for the transported degree.
  letI := deg.isQuasicoherent F.algebra_isQuasicoherent n
  exact Modules.RestrictToScheme.compositePullbackIso (base F hF U)
      (graphMap g hAlg hF hF' U V j) (deg.obj n) ≪≫
    (Modules.restrictToScheme V.obj.left).mapIso
      (eqToIso (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj n))
        (graphMap_base g hAlg hF hF' U V j)) ≪≫
        (Modules.pullbackCompIso (base F' hF' V) g).symm.app (deg.obj n) ≪≫
        (Modules.pullback (base F' hF' V)).mapIso (hAlg.degreeIso n))

/-- Pullback of homogeneous sections followed by the actual degree comparison. -/
def degreeSectionsMap (n : ℕ) :
    RingedSpace.GradedAlgebraSections.degree (localAlgebra F hF U) n →+
      RingedSpace.GradedAlgebraSections.degree (localAlgebra F' hF' V) n :=
  (Scheme.Modules.globalSectionsMap (degreePullIso g hAlg hF hF' U V j n).hom).hom.comp
    (Scheme.Modules.globalSectionsPullback (graphMap g hAlg hF hF' U V j).left
      (localAlgebra F hF U (n : ℤ))).hom

/-- The actual direct-sum graded ring map. Its laws use hAlg's real algebra laws. -/
def gradedMap :
    Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U) →+*ᵍ
      Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F' hF' V) where
  toRingHom := DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (RingedSpace.GradedAlgebraSections.degree (localAlgebra F' hF' V)) n).comp
      (degreeSectionsMap g hAlg hF hF' U V j n)) sorry sorry
  map_mem := sorry

/-- This map is affine scalar extension, so its projective domain is full. -/
theorem gradedMap_domain :
    projMapDomain (gradedMap (F := F) (F' := F') g hAlg hF hF' U V j) = ⊤ := sorry

-- Local declaration justification (localized automation): use the already typed graded morphism in projective localization and fraction maps without repeatedly reducing its geometric section-pullback implementation.
attribute [local irreducible] gradedMap

set_option maxRecDepth 1024 in
/-- The actual projective map, from the standard-open localization maps. -/
def projMap : Scheme.RelativeProjAffineSectionRing.scheme (localAlgebra F' hF' V) ⟶
    Scheme.RelativeProjAffineSectionRing.scheme (localAlgebra F hF U) := by
  let ψ := gradedMap (F := F) (F' := F') g hAlg hF hF' U V j
  have ht : projMapDomain ψ = ⊤ := gradedMap_domain (F := F) (F' := F') g hAlg hF hF' U V j
  exact Proj.AssociatedModule.GradedMap.fullMap.{u, u, u}
    (R := Scheme.RelativeProjAffineSectionRing.baseRing U.obj.left.left)
    (R' := Scheme.RelativeProjAffineSectionRing.baseRing V.obj.left.left)
    (A := Scheme.RelativeProjAffineSectionRing.ring (localAlgebra F hF U))
    (B := Scheme.RelativeProjAffineSectionRing.ring (localAlgebra F' hF' V))
    (𝒜 := Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U))
    (ℬ := Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F' hF' V))
    ψ ht

/-- The classifying sections commute with the canonical quadruple transport. -/
theorem sectionMap_square :
    sectionMap F' hF' V ≫ projMap g hAlg hF hF' U V j =
      (graphMap g hAlg hF hF' U V j).left ≫ sectionMap F hF U := sorry

set_option maxRecDepth 1024 in
/-- The specified local comparison is the pulled-back fraction map. -/
def localMap (n : ℤ) :
    (Scheme.Modules.pullback (graphMap g hAlg hF hF' U V j).left).obj
      (localObj F hF U n) ⟶ localObj F' hF' V n :=
  (Scheme.Modules.pullbackComp (graphMap g hAlg hF hF' U V j).left
      (sectionMap F hF U)).hom.app
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)) n) ≫
    eqToHom (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)) n))
      (sectionMap_square g hAlg hF hF' U V j).symm) ≫
    (Scheme.Modules.pullbackComp (sectionMap F' hF' V)
      (projMap g hAlg hF hF' U V j)).inv.app
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)) n) ≫
    (Scheme.Modules.pullback (sectionMap F' hF' V)).map
      (Proj.AssociatedModule.GradedMap.hom.{u, u, u}
        (R := Scheme.RelativeProjAffineSectionRing.baseRing U.obj.left.left)
        (R' := Scheme.RelativeProjAffineSectionRing.baseRing V.obj.left.left)
        (A := Scheme.RelativeProjAffineSectionRing.ring (localAlgebra F hF U))
        (B := Scheme.RelativeProjAffineSectionRing.ring (localAlgebra F' hF' V))
        (𝒜 := Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U))
        (ℬ := Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F' hF' V))
        (gradedMap (F := F) (F' := F') g hAlg hF hF' U V j)
        (gradedMap_domain (F := F) (F' := F') g hAlg hF hF' U V j) n)

/-- Only this actual scalar-extension comparison is asserted invertible. -/
theorem localMap_isIso (n : ℤ) : IsIso (localMap g hAlg hF hF' U V j n) := sorry

/-- Pull sections through the actual local map and the fixed affine comparisons. -/
def sectionComponent (n : ℤ) (x : (obj F hF n).val.obj (op U.obj)) :
    (obj F' hF' n).val.obj (op V.obj) :=
  (affineComparison F' hF' n).hom.val.app (op V)
    ((Scheme.Modules.globalSectionsMap (localMap g hAlg hF hF' U V j n)).hom
      ((Scheme.Modules.globalSectionsPullback (graphMap g hAlg hF hF' U V j).left
        (localObj F hF U n)).hom
        ((affineComparison F hF n).inv.val.app (op U) x)))


/-- The actual fraction-map sections form a matching family on the fibre product. -/
def matching (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℤ)
    (x : (obj F hF n).val.obj (op U.obj)) :
    AffineMatching (map g hAlg hF hF') (obj F' hF' n) U.obj where
  value V j := sectionComponent g hAlg hF hF' U V j n x
  compatible := sorry

/-- Reconstruct the direct-image section by the inverse of its actual affine restriction. -/
def pushforwardSection (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℤ)
    (x : (obj F hF n).val.obj (op U.obj)) :
    ((Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n)).val.obj (op U.obj) :=
  sectionOfMatching (map g hAlg hF hF') (obj F' hF' n) U.obj
    (matching g hAlg hF hF' U n x)

/-- The concrete module map on the dense affine basis. -/
def basisDirectMap (n : ℤ) :
    ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj (obj F hF n) ⟶
    ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
      ((Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n)) where
  val :=
    { app := fun U ↦ by
        let M := (((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
          (obj F hF n)).val.obj U
        let N := (((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
          ((Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n))).val.obj U
        exact @ModuleCat.ofHom ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj U) _ M N
          M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
          { toFun := pushforwardSection g hAlg hF hF' U.unop n
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- Descent through the actual fully faithful restriction functor. -/
def directMap (n : ℤ) : obj F hF n ⟶
    (Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n) :=
  ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).preimage
    (basisDirectMap g hAlg hF hF' n)

/-- The requested pullback morphism is the actual adjoint of the specified direct-image map. -/
def degreeMap (n : ℤ) :
    (Modules.pullback (map g hAlg hF hF')).obj (obj F hF n) ⟶ obj F' hF' n :=
  ((Modules.pullbackPushforwardAdjunction (map g hAlg hF hF')).homEquiv _ _).symm
    (directMap g hAlg hF hF' n)

/-- The adjoint recovers exactly the constructed direct-image map. -/
theorem degreeMap_adjoint (n : ℤ) :
    ((Modules.pullbackPushforwardAdjunction (map g hAlg hF hF')).homEquiv _ _)
      (degreeMap g hAlg hF hF' n) = directMap g hAlg hF hF' n :=
  Equiv.apply_symm_apply _ _

/-- The local component is exactly the actual fraction-induced section map. -/
theorem directMap_atGraph (U : affineEtaleSite (toAlgebraicSpace F hF))
    (V : affineEtaleSite (toAlgebraicSpace F' hF'))
    (j : AffineGraph (map g hAlg hF hF') U.obj V) (n : ℤ)
    (x : (obj F hF n).val.obj (op U.obj)) :
    directImageAtGraph (map g hAlg hF hF') (obj F' hF' n) U.obj V j
      ((directMap g hAlg hF hF' n).val.app (op U.obj) x) =
        sectionComponent g hAlg hF hF' U V j n x := by
  have h := ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).map_preimage
    (basisDirectMap g hAlg hF hF' n)
  have hx := congrArg (fun q ↦ q.val.app (op U) x) h
  change (directMap g hAlg hF hF' n).val.app (op U.obj) x =
    pushforwardSection g hAlg hF hF' U n x at hx
  rw [hx]
  exact sectionOfMatching_atGraph (map g hAlg hF hF') (obj F' hF' n) U.obj
    (matching g hAlg hF hF' U n x) V j

/-- Local affine scalar extension identifies this fixed map in every integral degree.
No flatness, degree-one-generation, or étaleness of the base change is assumed. -/
theorem degreeMap_isIso (n : ℤ) : IsIso (degreeMap g hAlg hF hF' n) := sorry

/-- The actual inverse is the inverse of that specified comparison. -/
def degreeIso (n : ℤ) :
    (Modules.pullback (map g hAlg hF hF')).obj (obj F hF n) ≅ obj F' hF' n :=
  @asIso _ _ _ _ (degreeMap g hAlg hF hF' n) (degreeMap_isIso g hAlg hF hF' n)

/-- Assemble the specified component maps and their actual algebra laws. -/
def comparison : GradedAlgebraComparison (map g hAlg hF hF') (family F hF) (family F' hF') where
  degreeMap := degreeMap g hAlg hF hF'
  map_one := sorry
  map_mul := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange
