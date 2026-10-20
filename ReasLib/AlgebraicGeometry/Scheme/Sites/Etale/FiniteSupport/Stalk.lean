module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.ResidueField
public import Mathlib.FieldTheory.Minpoly.Field
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct

/-!
# Stalk comparison for the compact-support presheaf

The canonical maps identifying the presheaf fibre of `f_{p!} F` at a geometric
point `ȳ` with the coproduct of the sheaf fibres of `F` at geometric points of
`X` over `ȳ`.
-/

@[expose] public section

open CategoryTheory hiding Over
open CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.Point
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

open FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [fQuasiFinite : LocallyQuasiFinite f]
  [fLocallyFiniteType : LocallyOfFiniteType f]
variable (ybar : GeometricPoint Y)

/-- The pairing lift of a geometric point of `X` over `ȳ` with a lift of `ȳ` to
an étale `Y`-scheme, as a morphism to `X_V`. -/
private def pairingSchemeHom {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (x : Fiber f ybar) :
    Spec (.of ybar.K) ⟶ baseChangeScheme f V :=
  pullback.lift v.left x.lift ((CategoryTheory.Over.w v).trans x.fac.symm)

/-- The pairing lift of a geometric point of `X` over `ȳ` with a lift of `ȳ` to
an étale `Y`-scheme, as a point of `X_V`. -/
private def pairingPoint {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (x : Fiber f ybar) : baseChangeScheme f V :=
  pairingSchemeHom f ybar v x (default : Spec (.of ybar.K))

/-- The point recorded by `SpecToEquivOfField` is the image of the unique point
of `Spec K`. -/
private theorem specToEquivOfField_fst_eq_apply {K : Type u} [Field K] {S : Scheme.{u}}
    (g : Spec (.of K) ⟶ S) :
    (SpecToEquivOfField K S g).1 = g default :=
  (Eq.trans
      (Scheme.fromSpecResidueField_apply (SpecToEquivOfField K S g).1
        (Spec.map (SpecToEquivOfField K S g).2 default)).symm
      (Scheme.Hom.comp_apply (Spec.map (SpecToEquivOfField K S g).2)
        (S.fromSpecResidueField (SpecToEquivOfField K S g).1) default).symm).trans
    (congrArg (fun h : Spec (.of K) ⟶ S ↦ h default)
      ((SpecToEquivOfField K S).left_inv g))

/-- Algebra structure on the field of `ȳ` over `κ(v)`, transported along the
fibre equality of a support point. -/
@[reducible]
private def supportBaseAlgebra {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z = v.left (default : Spec (.of ybar.K))) :
    Algebra (V.left.residueField ((LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z)) ybar.K :=
  ((V.left.residueFieldCongr
        (hz.trans (specToEquivOfField_fst_eq_apply v.left).symm)).hom ≫
      (SpecToEquivOfField ybar.K V.left v.left).2).hom.toAlgebra

/-- Algebra maps `κ(z) →ₐ[κ(v)] ȳ.K` at a fibre point of an admissible support. -/
private abbrev supportResidueAlgHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z = v.left (default : Spec (.of ybar.K))) :
    Type u :=
  @AlgHom
    (V.left.residueField ((LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z))
    ((LocallyClosedReduction.scheme A.subset).residueField z)
    ybar.K _ _ _
    (Scheme.Hom.residueFieldAlgebra ((LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V)) z)
    (supportBaseAlgebra f ybar v A z hz)

/-- There are only finitely many `κ(v)`-algebra maps from `κ(z)` into `ȳ.K`. -/
private theorem finite_supportResidueAlgHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z = v.left (default : Spec (.of ybar.K))) :
    Finite (supportResidueAlgHom f ybar v A z hz) :=
  @Finite.of_fintype _ <|
    @minpoly.AlgHom.fintype
      (V.left.residueField ((LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z))
      ((LocallyClosedReduction.scheme A.subset).residueField z) ybar.K
      _ _ _ _ (Scheme.Hom.residueFieldAlgebra _ z)
      (supportBaseAlgebra f ybar v A z hz)
      (Scheme.Hom.QuasiFiniteAt.moduleFinite_residueField
        (@Scheme.Hom.quasiFiniteAt _ _ _
          (@AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite _ _ _ A.toBase_isFinite) z))

/-- The finite set of `κ(v)`-algebra maps from `κ(z)` into `ȳ.K`. -/
private def supportResidueAlgHomFinset {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z = v.left (default : Spec (.of ybar.K))) :
    Finset (supportResidueAlgHom f ybar v A z hz) :=
  (Set.finite_univ_iff.mpr (finite_supportResidueAlgHom f ybar v A z hz)).toFinset

/-- The underlying ring homomorphism of a fibrewise residue-field algebra map. -/
private def supportResidueRingHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z = v.left (default : Spec (.of ybar.K)))
    (φ : supportResidueAlgHom f ybar v A z hz) :
    (LocallyClosedReduction.scheme A.subset).residueField z →+* ybar.K :=
  @AlgHom.toRingHom
    (V.left.residueField ((LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z))
    ((LocallyClosedReduction.scheme A.subset).residueField z)
    ybar.K _ _ _
    (Scheme.Hom.residueFieldAlgebra ((LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V)) z)
    (supportBaseAlgebra f ybar v A z hz) φ

/-- The `CommRingCat` morphism associated to a fibrewise residue-field algebra
map. -/
private def supportResidueCommRingHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z = v.left (default : Spec (.of ybar.K)))
    (φ : supportResidueAlgHom f ybar v A z hz) :
    (LocallyClosedReduction.scheme A.subset).residueField z ⟶ .of ybar.K :=
  CommRingCat.ofHom (supportResidueRingHom f ybar v A z hz φ)

/-- The geometric point of `X` over `ȳ` associated to a `κ(v)`-algebra map from
the residue field of a fibre point of an admissible support. -/
private def overOfSupportPoint {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z = v.left (default : Spec (.of ybar.K)))
    (φ : supportResidueAlgHom f ybar v A z hz) :
    Fiber f ybar :=
  Fiber.of
    (Spec.map (supportResidueCommRingHom f ybar v A z hz φ) ≫
        (LocallyClosedReduction.scheme A.subset).fromSpecResidueField z ≫
          LocallyClosedReduction.ι A.subset ≫ baseChangeToSource f V)
    (by sorry)

/-- The finite set of geometric points of `X` over `ȳ` lying on an admissible
support in the fibre of a lift of `ȳ`, obtained by taking every `κ(v)`-algebra
map from the residue field of each scheme point of the fibre. -/
private def supportOverFinset {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) : Finset (Fiber f ybar) :=
  let y0 := v.left (default : Spec (.of ybar.K))
  let g := LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V
  let hfin := @Scheme.Hom.finite_preimage_singleton _ _ g
    (@AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite _ _ g A.toBase_isFinite)
    (@AlgebraicGeometry.instQuasiCompactOfIsAffineHom _ _ g A.toBase_isFinite.toIsAffineHom) y0
  @Finset.biUnion _ _ (Classical.decEq _) hfin.toFinset.attach fun z ↦
    let hz : (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) z.1 = y0 :=
      Set.mem_singleton_iff.mp (Set.mem_preimage.mp (hfin.mem_toFinset.mp z.2))
    @Finset.image _ _ (Classical.decEq _) (fun ψ ↦
      overOfSupportPoint f ybar v A z.1 hz ψ)
      (supportResidueAlgHomFinset f ybar v A z.1 hz)

/-- Geometric points in `supportOverFinset` are those whose pairing with `v̄`
lies on the admissible support. -/
private theorem mem_supportOverFinset_iff {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    (x : Fiber f ybar) :
    x ∈ supportOverFinset f ybar v A ↔
      pairingPoint f ybar v x ∈ (A.subset : Set (baseChangeScheme f V)) :=
  sorry

/-- Membership in `supportOverFinset` implies that the pairing lands in the
ambient open of the admissible support. -/
private theorem supportOverFinset_mem_ambient {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    {x : Fiber f ybar} (hx : x ∈ supportOverFinset f ybar v A) :
    pairingPoint f ybar v x ∈ (A.ambient : Set _) :=
  sorry

/-- The étale `X`-scheme underlying the ambient open of an admissible support. -/
private def ambientEtale {V : Y.Etale} (A : Admissible f V) : X.Etale :=
  Etale.mk (Scheme.Opens.ι A.ambient ≫ baseChangeToSource f V)

/-- The pairing morphism of a geometric point in the ambient open factors through
that open immersion. -/
private theorem pairingSchemeHom_range_subset_ambient {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    (x : Fiber f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    Set.range (pairingSchemeHom f ybar v x) ⊆ Set.range A.ambient.ι :=
  sorry

/-- Open-immersion lift of a pairing into the ambient open of an admissible
support. -/
private def ambientOpenLift {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) (x : Fiber f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    Spec (.of ybar.K) ⟶ A.ambient.toScheme :=
  (A.ambient.instIsOpenImmersionι).lift A.ambient.ι
    (pairingSchemeHom f ybar v x)
    (pairingSchemeHom_range_subset_ambient f ybar v A x hx)

/-- The lift of a geometric point of `X` over `ȳ` to the ambient open of an
admissible support, when the pairing lands in that open. -/
private def ambientFiberLift {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) (x : Fiber f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    (toSmallEtalePoint x.point).fiber.obj (ambientEtale f A) :=
  CategoryTheory.Over.homMk (ambientOpenLift f ybar v A x hx) sorry

/-- Germ of an ambient supported section at a geometric point of `X` over `ȳ`. -/
private def supportGerm (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    (x : Fiber f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    sections f F A ⟶
      (toSmallEtalePoint x.point).sheafFiber.obj F :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        (toSmallEtalePoint x.point).toPresheafFiber
          (ambientEtale f A) (ambientFiberLift f ybar v A x hx) F.1 σ.1
      map_zero' := sorry
      map_add' := sorry }

/-- The map sending a supported section on `X_V` to the finite sum of its germs
at geometric points of the support over `ȳ`. -/
@[no_expose]
def supportToCoproduct (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) :
    sections f F A ⟶ (abelianStalkCoproduct f ybar).obj F :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        ∑ x ∈ (supportOverFinset f ybar v A).attach,
          (Sigma.ι (fun x : Fiber f ybar ↦
              (toSmallEtalePoint x.point).sheafFiber.obj F) x.1)
            (supportGerm f ybar F v A x.1
              (supportOverFinset_mem_ambient f ybar v A x.2) σ)
      map_zero' := sorry
      map_add' := sorry }

/-- Cocone of germ-sum maps from the finite-support diagram at an étale
neighbourhood of `ȳ`. -/
private def supportToCoproductCocone (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V) :
    Cocone (diagram f F V) :=
  Cocone.mk ((abelianStalkCoproduct f ybar).obj F)
    { app := fun A ↦ supportToCoproduct f ybar F v A
      naturality := sorry }

/-- The comparison out of `f_{p!} F(V)` obtained by summing germs of supported
sections. -/
@[no_expose]
def lowerShriekPresheafToCoproduct
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) :
    ((lowerShriekPresheaf f).obj F).obj (op V) ⟶
      (abelianStalkCoproduct f ybar).obj F :=
  colimit.desc (diagram f F V) (supportToCoproductCocone f ybar F v)

/-- Naturality of germ-sum comparisons on étale neighbourhoods of `ȳ`. -/
theorem lowerShriekPresheafToCoproduct_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V W : Y.Etale}
    (g : V ⟶ W) (v : (toSmallEtalePoint ybar).fiber.obj V) :
    ((lowerShriekPresheaf f).obj F).map g.op ≫
        lowerShriekPresheafToCoproduct f ybar F v =
      lowerShriekPresheafToCoproduct f ybar F
        ((toSmallEtalePoint ybar).fiber.map g v) :=
  sorry

/-- The canonical forward comparison `(f_{p!} F)_ȳ ⟶ ⊕_{f(x̄)=ȳ} F_x̄`, as a
natural transformation of functors in `F`. -/
def lowerShriekPresheafStalkComparison :
    lowerShriekPresheaf f ⋙ (toSmallEtalePoint ybar).presheafFiber ⟶
      abelianStalkCoproduct f ybar where
  app F :=
    (toSmallEtalePoint ybar).presheafFiberDesc
      (fun V v ↦ lowerShriekPresheafToCoproduct f ybar F v)
      (fun _ _ g v ↦ lowerShriekPresheafToCoproduct_naturality f ybar F g v)
  naturality := sorry

/-- Evaluating the forward comparison at an abelian étale sheaf. -/
theorem lowerShriekPresheafStalkComparison_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekPresheafStalkComparison f ybar).app F =
      (toSmallEtalePoint ybar).presheafFiberDesc
        (fun V v ↦ lowerShriekPresheafToCoproduct f ybar F v)
        (fun _ _ g v ↦ lowerShriekPresheafToCoproduct_naturality f ybar F g v) :=
  rfl

/-- The image of a geometric lift of `x̄` under `U ⟶ Y` is the image of `ȳ`. -/
private theorem finiteNeighborhood_comp_image_eq (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (U.hom ≫ f) (u.left (default : Spec (.of ybar.K))) = ybar.image :=
  sorry

include fQuasiFinite fLocallyFiniteType

/-- An étale neighbourhood admitting finite open components through the chosen fibre point. -/
@[irreducible]
private def finiteNeighborhood (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  let hType : LocallyOfFiniteType (U.hom ≫ f) :=
    @locallyOfFiniteType_comp _ _ _ U.hom f
      (@AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation _ _ U.hom
        (@AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth _ _ U.hom
          (@AlgebraicGeometry.Etale.instSmooth _ _ U.hom U.prop))) fLocallyFiniteType
  let hQuasi : LocallyQuasiFinite (U.hom ≫ f) :=
    MorphismProperty.comp_mem (@LocallyQuasiFinite) U.hom f
      (AlgebraicGeometry.Etale.locallyQuasiFinite U.prop) fQuasiFinite
  @exists_finiteOpen_etaleNeighborhoods_purelyInseparable _ _ (U.hom ≫ f) hType
    ybar.image 1 (fun _ ↦ u.left (default : Spec (.of ybar.K)))
    (fun _ ↦ finiteNeighborhood_comp_image_eq f ybar x U u)
    (fun {a b} _ ↦ Subsingleton.elim a b)
    (fun _ ↦ (@Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber _ _
      (U.hom ≫ f) hType _).mp
      (@Scheme.Hom.quasiFiniteAt _ _ (U.hom ≫ f) hQuasi
        (u.left (default : Spec (.of ybar.K)))))

/-- An étale neighbourhood of the image point with a finite-open decomposition. -/
private def finiteNeighborhoodOrdinary (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Scheme.EtaleNeighborhood Y ybar.image :=
  Classical.choose (finiteNeighborhood f ybar x U u)

/-- The étale scheme underlying the selected pointed neighbourhood. -/
private def finiteNeighborhoodBaseEtale (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) : Y.Etale :=
  (finiteNeighborhoodOrdinary f ybar x U u).toEtale

/-- The geometric base point lifts to the selected étale neighbourhood. -/
@[irreducible]
private def finiteNeighborhoodBaseLiftExists (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  @exists_fac_of_etale_of_isSepClosed _ _
    (finiteNeighborhoodBaseEtale f ybar x U u).hom
    (finiteNeighborhoodBaseEtale f ybar x U u).prop
    ybar.K _ (@IsSepClosed.of_isAlgClosed _ _ ybar.isAlgClosed) ybar.hom
    (finiteNeighborhoodOrdinary f ybar x U u).point
    (EtaleNeighborhood.map_point _)

/-- A lift of the geometric base point to the selected étale neighbourhood. -/
private def finiteNeighborhoodBaseLiftScheme (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Spec (.of ybar.K) ⟶ (finiteNeighborhoodBaseEtale f ybar x U u).left :=
  Classical.choose (finiteNeighborhoodBaseLiftExists f ybar x U u)

/-- The chosen lift of `ȳ` lies over `ȳ`. -/
private theorem finiteNeighborhoodBaseLiftScheme_fac (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    finiteNeighborhoodBaseLiftScheme f ybar x U u ≫
        (finiteNeighborhoodBaseEtale f ybar x U u).hom =
      ybar.hom :=
  (Classical.choose_spec (finiteNeighborhoodBaseLiftExists f ybar x U u)).1

/-- The chosen lift of `ȳ` hits the distinguished point of the neighbourhood. -/
private theorem finiteNeighborhoodBaseLiftScheme_apply (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    finiteNeighborhoodBaseLiftScheme f ybar x U u default =
      (finiteNeighborhoodOrdinary f ybar x U u).point :=
  (Classical.choose_spec (finiteNeighborhoodBaseLiftExists f ybar x U u)).2

/-- The pointed étale lift of the geometric base point. -/
private def finiteNeighborhoodBaseLift (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (toSmallEtalePoint ybar).fiber.obj
      (finiteNeighborhoodBaseEtale f ybar x U u) :=
  CategoryTheory.Over.homMk (finiteNeighborhoodBaseLiftScheme f ybar x U u)
    (finiteNeighborhoodBaseLiftScheme_fac f ybar x U u)

/-- Compatibility of the pairing lift into `U ×_Y V`. -/
private theorem finiteNeighborhoodPullbackLift_fac (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    u.left ≫ U.hom ≫ f =
      finiteNeighborhoodBaseLiftScheme f ybar x U u ≫
        (finiteNeighborhoodBaseEtale f ybar x U u).hom :=
  sorry

/-- The pairing of the two geometric lifts into the fibre product. -/
private def finiteNeighborhoodPullbackLift (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Spec (.of ybar.K) ⟶
      pullback (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom :=
  pullback.lift u.left (finiteNeighborhoodBaseLiftScheme f ybar x U u)
    (finiteNeighborhoodPullbackLift_fac f ybar x U u)

/-- The underlying point of the pairing of the geometric lifts. -/
private def finiteNeighborhoodPullbackPoint (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  finiteNeighborhoodPullbackLift f ybar x U u (default : Spec (.of ybar.K))

/-- The selected étale neighbourhood admits a finite-open decomposition with specified fibre points. -/
@[irreducible]
private def finiteNeighborhoodOrdinary_spec (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhood f ybar x U u)

/-- The numbers of finite-open components above the selected fibre points. -/
private def finiteNeighborhoodMultiplicity (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) : Fin 1 → ℕ :=
  Classical.choose (finiteNeighborhoodOrdinary_spec f ybar x U u)

/-- The chosen multiplicities retain the remaining finite-open witnesses. -/
@[irreducible]
private def finiteNeighborhoodMultiplicity_spec (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhoodOrdinary_spec f ybar x U u)

/-- The finite-open family of finite opens over the unique selected point. -/
private def finiteNeighborhoodFamily (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    ∀ i, Fin (finiteNeighborhoodMultiplicity f ybar x U u i) →
      (pullback (U.hom ≫ f)
        (finiteNeighborhoodBaseEtale f ybar x U u).hom).Opens :=
  Classical.choose (finiteNeighborhoodMultiplicity_spec f ybar x U u)

/-- The chosen open family retains its selected-point witnesses. -/
@[irreducible]
private def finiteNeighborhoodFamily_spec (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhoodMultiplicity_spec f ybar x U u)

/-- Selected fibre points of the finite-open family. -/
private def finiteNeighborhoodSelected (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    ∀ i (j : Fin (finiteNeighborhoodMultiplicity f ybar x U u i)),
      finiteNeighborhoodFamily f ybar x U u i j :=
  Classical.choose (finiteNeighborhoodFamily_spec f ybar x U u)

/-- The pairing of `x̄` with the étale neighbourhood lies over the
distinguished point of that neighbourhood. -/
private theorem finiteNeighborhoodPullbackPoint_snd (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (pullback.snd (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom)
        (finiteNeighborhoodPullbackPoint f ybar x U u) =
      (finiteNeighborhoodOrdinary f ybar x U u).point :=
  sorry

/-- The pairing of `x̄` with the étale neighbourhood maps to the original
lift of `x̄`. -/
private theorem finiteNeighborhoodPullbackPoint_fst (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (pullback.fst (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom)
        (finiteNeighborhoodPullbackPoint f ybar x U u) =
      u.left (default : Spec (.of ybar.K)) :=
  sorry

/-- The finite-open family has finite structure maps and the specified fibre decomposition. -/
@[irreducible]
private def finiteNeighborhoodInner (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhoodFamily_spec f ybar x U u)

/-- Each selected open component is finite over the étale neighbourhood. -/
private theorem finiteNeighborhoodFamily_isFinite (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    ∀ i j, IsFinite
      ((finiteNeighborhoodFamily f ybar x U u i j).ι ≫
        pullback.snd (U.hom ≫ f)
          (finiteNeighborhoodBaseEtale f ybar x U u).hom) :=
  Classical.choose (finiteNeighborhoodInner f ybar x U u)

/-- Exhaustiveness of the finite-open family over the unique selected point. -/
@[irreducible]
private def finiteNeighborhoodExhaust (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  Classical.choose_spec <|
    Classical.choose_spec <|
      Classical.choose_spec <|
        Classical.choose_spec <|
          Classical.choose_spec <|
            Classical.choose_spec <|
              Classical.choose_spec (finiteNeighborhoodInner f ybar x U u)

/-- The unique finite-open component containing the pairing of `x̄`. -/
private def finiteNeighborhoodIndex (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Fin (finiteNeighborhoodMultiplicity f ybar x U u (0 : Fin 1)) :=
  Classical.choose
    (finiteNeighborhoodExhaust f ybar x U u (0 : Fin 1)
      (finiteNeighborhoodPullbackPoint f ybar x U u)
      (finiteNeighborhoodPullbackPoint_snd f ybar x U u)
      (finiteNeighborhoodPullbackPoint_fst f ybar x U u))

/-- Finite open of `U ×_Y V` in the selected finite-open decomposition through the pairing of
`x̄`, namely the unique family component containing that pairing. -/
private def finiteNeighborhoodOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (pullback (U.hom ≫ f)
      (finiteNeighborhoodBaseEtale f ybar x U u).hom).Opens :=
  finiteNeighborhoodFamily f ybar x U u (0 : Fin 1)
    (finiteNeighborhoodIndex f ybar x U u)

/-- The selected selected finite open is finite over the étale neighbourhood. -/
private theorem finiteNeighborhoodOpen_isFinite (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsFinite
      ((finiteNeighborhoodOpen f ybar x U u).ι ≫
        pullback.snd (U.hom ≫ f)
          (finiteNeighborhoodBaseEtale f ybar x U u).hom) :=
  finiteNeighborhoodFamily_isFinite f ybar x U u (0 : Fin 1)
    (finiteNeighborhoodIndex f ybar x U u)

/-- The pairing of `x̄` is the selected fibre point of its finite-open
component. -/
private theorem finiteNeighborhoodIndex_spec (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    finiteNeighborhoodPullbackPoint f ybar x U u =
      (finiteNeighborhoodFamily f ybar x U u (0 : Fin 1)
          (finiteNeighborhoodIndex f ybar x U u)).ι
        (finiteNeighborhoodSelected f ybar x U u (0 : Fin 1)
          (finiteNeighborhoodIndex f ybar x U u)) :=
  sorry

/-- Selected fibre point of the selected finite open over `ȳ`. -/
private def finiteNeighborhoodPoint (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    finiteNeighborhoodOpen f ybar x U u :=
  ⟨finiteNeighborhoodPullbackPoint f ybar x U u, sorry⟩

/-- The selected finite-open component is finite over the base, has a unique
geometric point over `v̄`, and that point maps to the original lift of `x̄`. -/
private theorem finiteNeighborhoodOpen_spec (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsFinite
        ((finiteNeighborhoodOpen f ybar x U u).ι ≫
          pullback.snd (U.hom ≫ f)
            (finiteNeighborhoodBaseEtale f ybar x U u).hom) ∧
      (∀ w : finiteNeighborhoodOpen f ybar x U u,
        ((finiteNeighborhoodOpen f ybar x U u).ι ≫
              pullback.snd (U.hom ≫ f)
                (finiteNeighborhoodBaseEtale f ybar x U u).hom)
            w =
          (finiteNeighborhoodOrdinary f ybar x U u).point →
        w = finiteNeighborhoodPoint f ybar x U u) ∧
      pullback.fst (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom
          ((finiteNeighborhoodOpen f ybar x U u).ι
            (finiteNeighborhoodPoint f ybar x U u)) =
        u.left (default : Spec (.of ybar.K)) :=
  sorry

/-- The morphism from the selected finite open into the base change `X_V`. -/
private def finiteNeighborhoodToBaseChange (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (finiteNeighborhoodOpen f ybar x U u).toScheme ⟶
      baseChangeScheme f (finiteNeighborhoodBaseEtale f ybar x U u) :=
  (finiteNeighborhoodOpen f ybar x U u).ι ≫
    pullback.map (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom f
      (finiteNeighborhoodBaseEtale f ybar x U u).hom U.hom (𝟙 _) (𝟙 _)
      rfl
      ((Category.comp_id
          (finiteNeighborhoodBaseEtale f ybar x U u).hom).trans
        (Category.id_comp
          (finiteNeighborhoodBaseEtale f ybar x U u).hom).symm) ≫
    (pullbackSymmetry f (finiteNeighborhoodBaseEtale f ybar x U u).hom).hom

/-- Existence of an affine open of `X_V` containing the image of the selected pairing. -/
private theorem exists_sourceAmbientOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    ∃ W' : (baseChangeScheme f
        (finiteNeighborhoodBaseEtale f ybar x U u)).Opens,
      IsAffineOpen W' ∧
        finiteNeighborhoodToBaseChange f ybar x U u
            (finiteNeighborhoodPoint f ybar x U u) ∈ W' :=
  sorry

/-- Affine open `W'` of `X_V` containing the image of the selected pairing. -/
private def sourceAmbientOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (baseChangeScheme f (finiteNeighborhoodBaseEtale f ybar x U u)).Opens :=
  Classical.choose (exists_sourceAmbientOpen f ybar x U u)

/-- The chosen open of `X_V` is affine and contains the image of the pairing. -/
private theorem sourceAmbientOpen_spec (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsAffineOpen (sourceAmbientOpen f ybar x U u) ∧
      finiteNeighborhoodToBaseChange f ybar x U u
          (finiteNeighborhoodPoint f ybar x U u) ∈
        sourceAmbientOpen f ybar x U u :=
  Classical.choose_spec (exists_sourceAmbientOpen f ybar x U u)

/-- Points of the étale neighbourhood over which some point of the finite
open fails to land in `W'`. -/
private def finiteNeighborhoodEscape (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Set (finiteNeighborhoodOrdinary f ybar x U u).toEtale.left :=
  ((finiteNeighborhoodOpen f ybar x U u).ι ≫
      pullback.snd (U.hom ≫ f)
        (finiteNeighborhoodBaseEtale f ybar x U u).hom) ''
    (finiteNeighborhoodToBaseChange f ybar x U u ⁻¹'
      (sourceAmbientOpen f ybar x U u : Set _)ᶜ)

/-- Open of the étale neighbourhood over which the finite open lands in
the chosen ambient open of `X_V`. -/
private def shrunkBaseOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (finiteNeighborhoodOrdinary f ybar x U u).toEtale.left.Opens :=
  ⟨(finiteNeighborhoodEscape f ybar x U u)ᶜ, sorry⟩

/-- The distinguished point of the étale neighbourhood survives the
shrinking. -/
private theorem shrunkBaseOpen_mem_point (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (finiteNeighborhoodOrdinary f ybar x U u).point ∈
      shrunkBaseOpen f ybar x U u :=
  sorry

/-- The shrunk neighbourhood remains étale over `Y`. -/
private theorem shrunkBase_isEtale (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Etale
      ((shrunkBaseOpen f ybar x U u).ι ≫
        (finiteNeighborhoodBaseEtale f ybar x U u).hom) :=
  sorry

/-- Étale neighbourhood of `ȳ` obtained by shrinking the selected étale
neighbourhood so that the finite open lands in `W'`. -/
private def landingBaseEtale (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) : Y.Etale :=
  MorphismProperty.Over.mk _
    ((shrunkBaseOpen f ybar x U u).ι ≫
      (finiteNeighborhoodBaseEtale f ybar x U u).hom)
    (shrunkBase_isEtale f ybar x U u)

/-- Open immersion of the shrunk neighbourhood into the selected étale
neighbourhood. -/
private def shrunkBaseEtaleHom (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    landingBaseEtale f ybar x U u ⟶
      finiteNeighborhoodBaseEtale f ybar x U u :=
  MorphismProperty.Over.homMk (shrunkBaseOpen f ybar x U u).ι sorry

/-- Comparison of base changes `X_{V'} ⟶ X_V` along the shrinking. -/
private def shrunkBaseChangeMap (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    baseChangeScheme f (landingBaseEtale f ybar x U u) ⟶
      baseChangeScheme f (finiteNeighborhoodBaseEtale f ybar x U u) :=
  ((smallEtalePullback f).map (shrunkBaseEtaleHom f ybar x U u)).left

/-- Comparison of fibre products `U ×_Y V' ⟶ U ×_Y V` along the shrinking. -/
private def shrunkPullbackMap (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom ⟶
      pullback (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom :=
  pullback.map (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom
    (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom
    (𝟙 _) (shrunkBaseOpen f ybar x U u).ι (𝟙 _) rfl rfl

/-- The lift of `ȳ` to the étale neighbourhood factors through the
shrunk open. -/
private theorem finiteNeighborhoodBaseLiftScheme_range_subset_shrunk
    (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Set.range (finiteNeighborhoodBaseLiftScheme f ybar x U u) ⊆
      Set.range (shrunkBaseOpen f ybar x U u).ι :=
  sorry

/-- Geometric lift of `ȳ` to the shrunk neighbourhood, as a scheme morphism. -/
private def landingBaseLiftScheme (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Spec (.of ybar.K) ⟶ (landingBaseEtale f ybar x U u).left :=
  (shrunkBaseOpen f ybar x U u).instIsOpenImmersionι.lift
    (shrunkBaseOpen f ybar x U u).ι
    (finiteNeighborhoodBaseLiftScheme f ybar x U u)
    (finiteNeighborhoodBaseLiftScheme_range_subset_shrunk f ybar x U u)

/-- The chosen lift of `ȳ` to the shrunk neighbourhood lies over `ȳ`. -/
private theorem landingBaseLiftScheme_fac (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    landingBaseLiftScheme f ybar x U u ≫ (landingBaseEtale f ybar x U u).hom =
      ybar.hom :=
  sorry

/-- Geometric lift of `ȳ` to the shrunk étale neighbourhood. -/
private def landingBaseLift (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (toSmallEtalePoint ybar).fiber.obj (landingBaseEtale f ybar x U u) :=
  CategoryTheory.Over.homMk (landingBaseLiftScheme f ybar x U u)
    (landingBaseLiftScheme_fac f ybar x U u)

/-- The selected finite open, pulled back to the shrunk neighbourhood. -/
private def landingFiniteOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom).Opens :=
  shrunkPullbackMap f ybar x U u ⁻¹ᵁ finiteNeighborhoodOpen f ybar x U u

/-- The once-shrunk selected finite open remains finite over the shrunk base, as a
base change of `finiteNeighborhoodOpen_isFinite`. -/
private theorem landingFiniteOpen_isFinite (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsFinite
      ((landingFiniteOpen f ybar x U u).ι ≫
        pullback.snd (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom) :=
  sorry

/-- The affine open `W'` of `X_V`, pulled back to `X_{V'}`. -/
private def sourceAmbientShrunk (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (baseChangeScheme f (landingBaseEtale f ybar x U u)).Opens :=
  shrunkBaseChangeMap f ybar x U u ⁻¹ᵁ sourceAmbientOpen f ybar x U u

/-- The morphism from the pulled-back finite open into `X_{V'}`. -/
private def landingFiniteToBaseChange (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (landingFiniteOpen f ybar x U u).toScheme ⟶
      baseChangeScheme f (landingBaseEtale f ybar x U u) :=
  (landingFiniteOpen f ybar x U u).ι ≫
    pullback.map (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom f
      (landingBaseEtale f ybar x U u).hom U.hom (𝟙 _) (𝟙 _)
      rfl
      ((Category.comp_id (landingBaseEtale f ybar x U u).hom).trans
        (Category.id_comp (landingBaseEtale f ybar x U u).hom).symm) ≫
    (pullbackSymmetry f (landingBaseEtale f ybar x U u).hom).hom

/-- After shrinking, the finite open lands in `W'`. -/
private theorem landingFiniteToBaseChange_range_subset_ambient
    (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Set.range (landingFiniteToBaseChange f ybar x U u) ⊆
      Set.range (sourceAmbientShrunk f ybar x U u).ι :=
  sorry

/-- Finite étale map from the shrunk selected finite open into `W' ⊂ X_{V'}`. -/
private def finiteToAmbient (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (landingFiniteOpen f ybar x U u).toScheme ⟶
      (sourceAmbientShrunk f ybar x U u).toScheme :=
  (sourceAmbientShrunk f ybar x U u).instIsOpenImmersionι.lift
    (sourceAmbientShrunk f ybar x U u).ι
    (landingFiniteToBaseChange f ybar x U u)
    (landingFiniteToBaseChange_range_subset_ambient f ybar x U u)

/-- After shrinking, the map into `W'` is finite. -/
private theorem finiteToAmbient_isFinite (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsFinite (finiteToAmbient f ybar x U u) :=
  sorry

/-- After shrinking, the map into `W'` is étale. -/
private theorem finiteToAmbient_isEtale (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Etale (finiteToAmbient f ybar x U u) :=
  sorry

/-- Compatibility of the pairing lift into `U ×_Y V'` after shrinking. -/
private theorem landingPullbackLift_fac (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    u.left ≫ U.hom ≫ f =
      landingBaseLiftScheme f ybar x U u ≫
        (landingBaseEtale f ybar x U u).hom :=
  sorry

/-- The pairing morphism of the lift of `x̄` with the shrunk neighbourhood. -/
private def landingPullbackLift (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Spec (.of ybar.K) ⟶
      pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom :=
  pullback.lift u.left (landingBaseLiftScheme f ybar x U u)
    (landingPullbackLift_fac f ybar x U u)

/-- The pairing of `x̄`, as a point of the shrunk finite open. -/
private def finiteToAmbientPoint (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    landingFiniteOpen f ybar x U u :=
  ⟨landingPullbackLift f ybar x U u (default : Spec (.of ybar.K)), sorry⟩

/-- Image of the pairing in the shrunk ambient open `W'`. -/
private def ambientImagePoint (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    sourceAmbientShrunk f ybar x U u :=
  finiteToAmbient f ybar x U u (finiteToAmbientPoint f ybar x U u)

/-- After shrinking, the finite étale map into `W'` has a unique point over the
image of the pairing. -/
private theorem finiteToAmbient_uniqueFiber (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    finiteToAmbient f ybar x U u ⁻¹'
        {ambientImagePoint f ybar x U u} =
      {finiteToAmbientPoint f ybar x U u} :=
  sorry

/-- The residue-field extension of the finite étale map into `W'` at the pairing
is purely inseparable. -/
private theorem finiteToAmbient_purelyInseparable (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    ((Scheme.residueFieldCongr rfl).inv ≫
        (finiteToAmbient f ybar x U u).residueFieldMap
          (finiteToAmbientPoint f ybar x U u)).hom.IsPurelyInseparable :=
  sorry

/-- The finite étale morphism is an isomorphism on an open neighbourhood of the distinguished image point. -/
@[irreducible]
private def isoNeighborhoodExists (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :=
  @AlgebraicGeometry.Etale.exists_isIso_morphismRestrict _ _
    (finiteToAmbient f ybar x U u)
    (finiteToAmbient_isFinite f ybar x U u)
    (finiteToAmbient_isEtale f ybar x U u)
    (ambientImagePoint f ybar x U u)
    (finiteToAmbientPoint f ybar x U u) rfl
    (finiteToAmbient_uniqueFiber f ybar x U u)
    (finiteToAmbient_purelyInseparable f ybar x U u)

/-- An open neighbourhood on which the finite étale morphism restricts to an isomorphism. -/
private def isoNeighborhoodOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (sourceAmbientShrunk f ybar x U u).toScheme.Opens :=
  Classical.choose (isoNeighborhoodExists f ybar x U u)

/-- The chosen open of `W'` contains the image of the pairing and makes the
finite étale map an isomorphism. -/
private theorem isoNeighborhoodOpen_spec (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    ambientImagePoint f ybar x U u ∈ isoNeighborhoodOpen f ybar x U u ∧
      IsIso
        (finiteToAmbient f ybar x U u ∣_
          isoNeighborhoodOpen f ybar x U u) :=
  Classical.choose_spec (isoNeighborhoodExists f ybar x U u)

/-- The image of the isomorphism neighbourhood in the once-shrunk base change. -/
private def landingIsoAmbientOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (baseChangeScheme f (landingBaseEtale f ybar x U u)).Opens :=
  (sourceAmbientShrunk f ybar x U u).ι ''ᵁ
    isoNeighborhoodOpen f ybar x U u

/-- The base points below points outside the isomorphism locus. -/
private def isoNeighborhoodEscape (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Set (landingBaseEtale f ybar x U u).left :=
  ((landingFiniteOpen f ybar x U u).ι ≫
      pullback.snd (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom) ''
    (finiteToAmbient f ybar x U u ⁻¹'
      (isoNeighborhoodOpen f ybar x U u : Set _)ᶜ)

/-- The complement of the closed image of the finite open outside the isomorphism locus. -/
private def isoBaseOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (landingBaseEtale f ybar x U u).left.Opens :=
  ⟨(isoNeighborhoodEscape f ybar x U u)ᶜ, sorry⟩

/-- The lift of `ȳ` to the once-shrunk neighbourhood survives the second
shrinking. -/
private theorem isoBaseOpen_mem_point (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    landingBaseLiftScheme f ybar x U u default ∈ isoBaseOpen f ybar x U u :=
  sorry

/-- The twice-shrunk neighbourhood remains étale over `Y`. -/
private theorem isoBase_isEtale (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Etale
      ((isoBaseOpen f ybar x U u).ι ≫
        (landingBaseEtale f ybar x U u).hom) :=
  sorry

/-- Étale neighbourhood of `ȳ` obtained by shrinking `V` and `W'` until the
finite open maps isomorphically onto the pulled-back isomorphism locus. -/
private def inverseBaseEtale (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) : Y.Etale :=
  MorphismProperty.Over.mk _
    ((isoBaseOpen f ybar x U u).ι ≫
      (landingBaseEtale f ybar x U u).hom)
    (isoBase_isEtale f ybar x U u)

/-- Open immersion of the twice-shrunk neighbourhood into the once-shrunk
neighbourhood. -/
private def isoBaseEtaleHom (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    inverseBaseEtale f ybar x U u ⟶ landingBaseEtale f ybar x U u :=
  MorphismProperty.Over.homMk (isoBaseOpen f ybar x U u).ι sorry

/-- Comparison of base changes `X_{V''} ⟶ X_{V'}` along the second shrinking. -/
private def isoBaseChangeMap (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    baseChangeScheme f (inverseBaseEtale f ybar x U u) ⟶
      baseChangeScheme f (landingBaseEtale f ybar x U u) :=
  ((smallEtalePullback f).map (isoBaseEtaleHom f ybar x U u)).left

/-- Comparison of fibre products `U ×_Y V'' ⟶ U ×_Y V'` along the second
shrinking. -/
private def isoPullbackMap (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    pullback (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom ⟶
      pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom :=
  pullback.map (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom
    (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom
    (𝟙 _) (isoBaseOpen f ybar x U u).ι (𝟙 _) rfl rfl

/-- The lift of `ȳ` to the once-shrunk neighbourhood factors through the second
shrinking. -/
private theorem landingBaseLiftScheme_range_subset_iso (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Set.range (landingBaseLiftScheme f ybar x U u) ⊆
      Set.range (isoBaseOpen f ybar x U u).ι :=
  sorry

/-- Geometric lift of `ȳ` to the twice-shrunk neighbourhood, as a scheme
morphism. -/
private def inverseBaseLiftScheme (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Spec (.of ybar.K) ⟶ (inverseBaseEtale f ybar x U u).left :=
  (isoBaseOpen f ybar x U u).instIsOpenImmersionι.lift
    (isoBaseOpen f ybar x U u).ι
    (landingBaseLiftScheme f ybar x U u)
    (landingBaseLiftScheme_range_subset_iso f ybar x U u)

/-- The chosen lift of `ȳ` to the twice-shrunk neighbourhood lies over `ȳ`. -/
private theorem inverseBaseLiftScheme_fac (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    inverseBaseLiftScheme f ybar x U u ≫ (inverseBaseEtale f ybar x U u).hom =
      ybar.hom :=
  sorry

/-- Geometric lift of `ȳ` to the twice-shrunk étale neighbourhood. -/
private def inverseBaseLift (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (toSmallEtalePoint ybar).fiber.obj (inverseBaseEtale f ybar x U u) :=
  CategoryTheory.Over.homMk (inverseBaseLiftScheme f ybar x U u)
    (inverseBaseLiftScheme_fac f ybar x U u)

/-- The selected finite open, pulled back to the twice-shrunk
neighbourhood. -/
private def inverseFiniteOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (pullback (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom).Opens :=
  isoPullbackMap f ybar x U u ⁻¹ᵁ landingFiniteOpen f ybar x U u

/-- The twice-shrunk finite open remains finite over the twice-shrunk base, as a
base change of `landingFiniteOpen_isFinite` and hence of
`finiteNeighborhoodOpen_isFinite`. -/
private theorem inverseFiniteOpen_isFinite (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsFinite
      ((inverseFiniteOpen f ybar x U u).ι ≫
        pullback.snd (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom) :=
  sorry

/-- The isomorphism neighbourhood of `W'`, pulled back to `X_{V''}`. After the second
shrinking this is the open subscheme of `X_{V''}` isomorphic to the pulled-back
finite open. -/
private def inverseAmbientOpen (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (baseChangeScheme f (inverseBaseEtale f ybar x U u)).Opens :=
  isoBaseChangeMap f ybar x U u ⁻¹ᵁ landingIsoAmbientOpen f ybar x U u

/-- The morphism from the twice-shrunk finite open into `X_{V''}`. -/
private def inverseFiniteToBaseChange (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (inverseFiniteOpen f ybar x U u).toScheme ⟶
      baseChangeScheme f (inverseBaseEtale f ybar x U u) :=
  (inverseFiniteOpen f ybar x U u).ι ≫
    pullback.map (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom f
      (inverseBaseEtale f ybar x U u).hom U.hom (𝟙 _) (𝟙 _)
      rfl
      ((Category.comp_id (inverseBaseEtale f ybar x U u).hom).trans
        (Category.id_comp (inverseBaseEtale f ybar x U u).hom).symm) ≫
    (pullbackSymmetry f (inverseBaseEtale f ybar x U u).hom).hom

/-- After the second shrinking, the finite open lands in the pulled-back
isomorphism locus. -/
private theorem inverseFiniteToBaseChange_range_subset_ambient
    (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Set.range (inverseFiniteToBaseChange f ybar x U u) ⊆
      Set.range (inverseAmbientOpen f ybar x U u).ι :=
  sorry

/-- The morphism from the twice-shrunk finite open to the original étale
neighbourhood of `x̄`. -/
private def inverseFiniteToU (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (inverseFiniteOpen f ybar x U u).toScheme ⟶ U.left :=
  (inverseFiniteOpen f ybar x U u).ι ≫
    pullback.fst (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom

/-- After the second shrinking, the finite open maps to the pulled-back
isomorphism locus `W' ⊂ X_{V''}`. -/
private def inverseFiniteToAmbient (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (inverseFiniteOpen f ybar x U u).toScheme ⟶
      (inverseAmbientOpen f ybar x U u).toScheme :=
  (inverseAmbientOpen f ybar x U u).instIsOpenImmersionι.lift
    (inverseAmbientOpen f ybar x U u).ι
    (inverseFiniteToBaseChange f ybar x U u)
    (inverseFiniteToBaseChange_range_subset_ambient f ybar x U u)

/-- The lift of the twice-shrunk finite open into `W'` recovers the open
immersion into `X_{V''}`. -/
private theorem inverseFiniteToAmbient_ι (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    inverseFiniteToAmbient f ybar x U u ≫
        (inverseAmbientOpen f ybar x U u).ι =
      inverseFiniteToBaseChange f ybar x U u :=
  sorry

-- Restriction domains agree by unfolding the private open-shrinking definitions.
set_option backward.isDefEq.respectTransparency false in
/-- The twice-shrunk finite open is isomorphic to the pulled-back ambient open. -/
private def inverseFiniteToAmbientIso (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (inverseFiniteOpen f ybar x U u).toScheme ≅
      (inverseAmbientOpen f ybar x U u).toScheme := by
  let g := finiteToAmbient f ybar x U u
  let O := isoNeighborhoodOpen f ybar x U u
  let e := @asIso _ _ _ _ (g ∣_ O) (isoNeighborhoodOpen_spec f ybar x U u).2
  let a : (inverseAmbientOpen f ybar x U u).toScheme ⟶ O.toScheme :=
    (isoBaseChangeMap f ybar x U u ∣_ landingIsoAmbientOpen f ybar x U u) ≫
    ((sourceAmbientShrunk f ybar x U u).ι.isoImage O).inv
  let b : (inverseAmbientOpen f ybar x U u).toScheme ⟶
      (landingFiniteOpen f ybar x U u).toScheme := a ≫ e.inv ≫ (g ⁻¹ᵁ O).ι
  have hb : b ≫ g ≫ (sourceAmbientShrunk f ybar x U u).ι =
      (inverseAmbientOpen f ybar x U u).ι ≫ isoBaseChangeMap f ybar x U u := by
    dsimp only [b]
    simp only [Category.assoc]
    rw [← Category.assoc (g ⁻¹ᵁ O).ι g,
      ← morphismRestrict_ι]
    simp only [Category.assoc]
    have he : e.inv ≫ (g ∣_ O) = 𝟙 _ := e.inv_hom_id
    rw [← Category.assoc e.inv (g ∣_ O), he]
    simp only [Category.id_comp]
    dsimp only [a]
    simp only [Category.assoc]
    rw [Scheme.Hom.isoImage_inv_ι]
    exact morphismRestrict_ι (isoBaseChangeMap f ybar x U u)
      (landingIsoAmbientOpen f ybar x U u)
  have hbBase : b ≫ (landingFiniteOpen f ybar x U u).ι ≫
        pullback.snd (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom =
      (inverseAmbientOpen f ybar x U u).ι ≫
        baseChangeToBase f (inverseBaseEtale f ybar x U u) ≫
          (isoBaseOpen f ybar x U u).ι := by
    have h := congrArg (fun k ↦ k ≫ baseChangeToBase f (landingBaseEtale f ybar x U u)) hb
    simpa [g, finiteToAmbient, landingFiniteToBaseChange, isoBaseChangeMap,
      isoBaseEtaleHom, baseChangeToBase, Category.assoc,
      IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac_assoc,
      pullbackSymmetry_hom_comp_fst, pullback.map,
      pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h
  let c : (inverseAmbientOpen f ybar x U u).toScheme ⟶
      pullback (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom := pullback.lift
    (b ≫ (landingFiniteOpen f ybar x U u).ι ≫
      pullback.fst (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom)
    ((inverseAmbientOpen f ybar x U u).ι ≫
      baseChangeToBase f (inverseBaseEtale f ybar x U u))
    (by
      calc
        (b ≫ (landingFiniteOpen f ybar x U u).ι ≫
            pullback.fst (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom) ≫
            (U.hom ≫ f) =
          (b ≫ (landingFiniteOpen f ybar x U u).ι ≫
            pullback.snd (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom) ≫
              (landingBaseEtale f ybar x U u).hom := by
                simp only [Category.assoc, pullback.condition]
        _ = _ := by rw [hbBase]; simp only [Category.assoc]; rfl)
  have hc : c ≫ isoPullbackMap f ybar x U u =
      b ≫ (landingFiniteOpen f ybar x U u).ι := by
    apply pullback.hom_ext
    · dsimp only [c, isoPullbackMap, pullback.map]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id]
    · dsimp only [c, isoPullbackMap, pullback.map]
      simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      simpa only [Category.assoc] using hbBase.symm
  let inverse := (inverseFiniteOpen f ybar x U u).instIsOpenImmersionι.lift
    (inverseFiniteOpen f ybar x U u).ι c (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change isoPullbackMap f ybar x U u (c z) ∈ landingFiniteOpen f ybar x U u
      rw [← Scheme.Hom.comp_apply, hc]
      exact (b z).property)
  exact
    { hom := inverseFiniteToAmbient f ybar x U u
      inv := inverse
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- The canonical morphism from the twice-shrunk finite open to the ambient open is invertible. -/
private theorem inverseFiniteToAmbient_isIso (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsIso (inverseFiniteToAmbient f ybar x U u) :=
  ⟨⟨(inverseFiniteToAmbientIso f ybar x U u).inv,
    (inverseFiniteToAmbientIso f ybar x U u).hom_inv_id,
    (inverseFiniteToAmbientIso f ybar x U u).inv_hom_id⟩⟩

/-- Scheme morphism from the pulled-back `W'` to the original étale neighbourhood
of `x̄`, via the isomorphism with the twice-shrunk finite open. -/
private def inverseAmbientToUScheme (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    (inverseAmbientOpen f ybar x U u).toScheme ⟶ U.left :=
  (inverseFiniteToAmbientIso f ybar x U u).inv ≫
    inverseFiniteToU f ybar x U u

/-- The pulled-back `W'` is étale over `X`. -/
private theorem inverseAmbient_isEtale (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    Etale
      ((inverseAmbientOpen f ybar x U u).ι ≫
        baseChangeToSource f (inverseBaseEtale f ybar x U u)) :=
  sorry

/-- Restriction morphism of small-étale `X`-schemes from the pulled-back `W'` to
the original neighbourhood of `x̄`. -/
private def inverseAmbientToU (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    MorphismProperty.Over.mk _
        ((inverseAmbientOpen f ybar x U u).ι ≫
          baseChangeToSource f (inverseBaseEtale f ybar x U u))
        (inverseAmbient_isEtale f ybar x U u) ⟶
      U :=
  MorphismProperty.Over.homMk (inverseAmbientToUScheme f ybar x U u) sorry

/-- The pulled-back `W'` is finite over the twice-shrunk neighbourhood, by
transporting `inverseFiniteOpen_isFinite` along `W ≅ W'`. -/
private theorem inverseAmbient_isFinite (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U) :
    IsFinite
      ((inverseAmbientOpen f ybar x U u).ι ≫
        baseChangeToBase f (inverseBaseEtale f ybar x U u)) :=
  sorry

/-- Finite-support pair on the twice-shrunk neighbourhood associated to a section
of `F` on an étale neighbourhood of `x̄`. The subscheme is the pulled-back `W'`,
isomorphic to the selected finite open after the second shrinking. -/
private def inverseSupportTerm (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U)
    (s : F.1.obj (op U)) :
    FiniteSupportTerm f F (inverseBaseEtale f ybar x U u) :=
  @FiniteSupportTerm.of X Y f F (inverseBaseEtale f ybar x U u)
    (inverseAmbientOpen f ybar x U u).toScheme
    (inverseAmbientOpen f ybar x U u).ι inferInstance
    (inverseAmbient_isFinite f ybar x U u)
    (inverseAmbientOpen f ybar x U u)
    sorry
    sorry
    ((F.1.map (inverseAmbientToU f ybar x U u).op).hom s)
    sorry

/-- The inverse support term is finite over the twice-shrunk base and isomorphic to the pulled-back finite open. -/
private theorem inverseSupportTerm_spec (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (x : Fiber f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.point).fiber.obj U)
    (s : F.1.obj (op U)) :
    (inverseSupportTerm f ybar F x U u s).subscheme =
        (inverseAmbientOpen f ybar x U u).toScheme ∧
      IsFinite
        ((inverseSupportTerm f ybar F x U u s).ι ≫
          baseChangeToBase f (inverseBaseEtale f ybar x U u)) ∧
      IsIso (inverseFiniteToAmbient f ybar x U u) :=
  sorry

/-- The stalk map `F_x̄ ⟶ (f_{p!} F)_ȳ` sending a germ on an étale neighbourhood
of `x̄` to the germ of the corresponding finite-support pair. -/
@[no_expose]
def stalkToLowerShriekPresheafFiber
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Fiber f ybar) :
    (toSmallEtalePoint x.point).sheafFiber.obj F ⟶
      (toSmallEtalePoint ybar).presheafFiber.obj ((lowerShriekPresheaf f).obj F) :=
  (toSmallEtalePoint x.point).presheafFiberDesc
    (fun U u ↦
      AddCommGrpCat.ofHom
        { toFun := fun s ↦
            (toSmallEtalePoint ybar).toPresheafFiber
              (inverseBaseEtale f ybar x U u)
              (inverseBaseLift f ybar x U u)
              ((lowerShriekPresheaf f).obj F)
              (ofTerm f F (inverseBaseEtale f ybar x U u)
                (inverseSupportTerm f ybar F x U u s))
          map_zero' := sorry
          map_add' := sorry })
    sorry

/-- The germ of a section on an étale neighbourhood of `x̄` is sent to the germ of
the corresponding finite-support pair on the twice-shrunk neighbourhood. -/
private theorem stalkToLowerShriekPresheafFiber_germ
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Fiber f ybar)
    (U : X.Etale) (u : (toSmallEtalePoint x.point).fiber.obj U)
    (s : F.1.obj (op U)) :
    stalkToLowerShriekPresheafFiber f ybar F x
        ((toSmallEtalePoint x.point).toPresheafFiber U u F.1 s) =
      (toSmallEtalePoint ybar).toPresheafFiber
        (inverseBaseEtale f ybar x U u)
        (inverseBaseLift f ybar x U u)
        ((lowerShriekPresheaf f).obj F)
        (ofTerm f F (inverseBaseEtale f ybar x U u)
          (inverseSupportTerm f ybar F x U u s)) :=
  sorry

/-- The canonical inverse comparison `⊕_{f(x̄)=ȳ} F_x̄ ⟶ (f_{p!} F)_ȳ`. -/
def lowerShriekPresheafStalkComparisonInv :
    abelianStalkCoproduct f ybar ⟶
      lowerShriekPresheaf f ⋙ (toSmallEtalePoint ybar).presheafFiber where
  app F :=
    Sigma.desc fun x : Fiber f ybar ↦
      stalkToLowerShriekPresheafFiber f ybar F x
  naturality := sorry

/-- Evaluating the inverse comparison at an abelian étale sheaf. -/
theorem lowerShriekPresheafStalkComparisonInv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekPresheafStalkComparisonInv f ybar).app F =
      Sigma.desc fun x : Fiber f ybar ↦
        stalkToLowerShriekPresheafFiber f ybar F x :=
  rfl

/-- The germ of a finite-support pair at an étale neighbourhood of `ȳ` is sent
to the finite sum of the germs of its section at geometric points of the
support over `ȳ`. -/
theorem lowerShriekPresheafStalkComparison_germ
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (t : FiniteSupportTerm f F V) :
    (lowerShriekPresheafStalkComparison f ybar).app F
        ((toSmallEtalePoint ybar).toPresheafFiber V v ((lowerShriekPresheaf f).obj F)
          (ofTerm f F V t)) =
      supportToCoproduct f ybar F v (Admissible.ofTerm f t)
        ⟨t.sec, t.mem_sectionsSupportedIn⟩ :=
  sorry

/-- The finite-support presheaf stalk is naturally isomorphic to the coproduct of
abelian étale stalks at the same-field geometric lifts. -/
@[stacks 0F6P]
def lowerShriekPresheafStalkIso :
    lowerShriekPresheaf f ⋙ (toSmallEtalePoint ybar).presheafFiber ≅
      abelianStalkCoproduct f ybar where
  hom := lowerShriekPresheafStalkComparison f ybar
  inv := lowerShriekPresheafStalkComparisonInv f ybar
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The component of the finite-support stalk isomorphism at an abelian étale sheaf. -/
def lowerShriekPresheafStalkIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).presheafFiber.obj ((lowerShriekPresheaf f).obj F) ≅
      (abelianStalkCoproduct f ybar).obj F :=
  (lowerShriekPresheafStalkIso f ybar).app F

/-- The forward map of `lowerShriekPresheafStalkIso` is the germ-sum comparison. -/
theorem lowerShriekPresheafStalkIso_hom :
    (lowerShriekPresheafStalkIso f ybar).hom =
      lowerShriekPresheafStalkComparison f ybar :=
  rfl

/-- The inverse map of `lowerShriekPresheafStalkIso` is the coproduct of stalk
maps from finite étale neighbourhoods. -/
theorem lowerShriekPresheafStalkIso_inv :
    (lowerShriekPresheafStalkIso f ybar).inv =
      lowerShriekPresheafStalkComparisonInv f ybar :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
