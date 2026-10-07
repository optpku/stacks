module

public import stacks_project.Chap71.Lemma_71_11_5_TwistAlgebra
public import stacks_project.Chap71.Lemma_71_11_5_TwistPushforward
public import stacks_project.Chap71.Lemma_71_11_5_Pointwise

/-!
# Local components of the actual canonical twist base-change map

An affine test of P' over the fibre product with an affine test of P gives an
actual scheme map. Its homogeneous-section map uses the supplied genuine
algebra pullback, with its unit and multiplication laws. The resulting Serre
comparison is the explicit fraction map on the actual graded section rings.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
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

-- The two-base graded-map expression exceeds Lean's default elaboration depth512
-- (private checks1791166643675375291/1791166881619298578). The same explicit
-- data compile at depth1024; proof heartbeats and kernel checking are unchanged.
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

/-- The actual classifying sections obey the source's quadruple formula. -/
theorem sectionMap_square :
    sectionMap F' hF' V ≫ projMap g hAlg hF hF' U V j =
      (graphMap g hAlg hF hF' U V j).left ≫ sectionMap F hF U := sorry

-- The local comparison contains the same two-base graded-map expression.
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
instance localMap_isIso (n : ℤ) : IsIso (localMap g hAlg hF hF' U V j n) := sorry

/-- Pull sections through the actual local map and the fixed affine comparisons. -/
def sectionComponent (n : ℤ) (x : (obj F hF n).val.obj (op U.obj)) :
    (obj F' hF' n).val.obj (op V.obj) :=
  (affineComparison F' hF' n).hom.val.app (op V)
    ((Scheme.Modules.globalSectionsMap (localMap g hAlg hF hF' U V j n)).hom
      ((Scheme.Modules.globalSectionsPullback (graphMap g hAlg hF hF' U V j).left
        (localObj F hF U n)).hom
        ((affineComparison F hF n).inv.val.app (op U) x)))

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange
