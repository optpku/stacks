module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
public import stacks_project.Chap63.«63_4_0_2_LowerShriekPresheaf»
public import stacks_project.Chap63.Lemma_63_4_2_StalkCoproduct

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

/-- The structure morphism of an object of the small étale site is étale. -/
instance etale_hom {S : Scheme.{u}} (V : S.Etale) : Etale V.hom :=
  V.prop

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]
variable (ybar : GeometricPoint Y)

/-- An étale morphism of `X`-schemes remains locally of finite type after
composing with a locally of finite type morphism. -/
instance locallyOfFiniteType_etale_comp (U : X.Etale) :
    LocallyOfFiniteType (U.hom ≫ f) :=
  sorry

/-- An étale `X`-scheme remains locally quasi-finite after composing with a
locally quasi-finite morphism. -/
instance locallyQuasiFinite_etale_comp (U : X.Etale) :
    LocallyQuasiFinite (U.hom ≫ f) :=
  sorry

/-- Residue-field maps of scheme morphisms induce algebra structures. -/
instance algebra_residueField {Z V : Scheme.{u}} (g : Z ⟶ V) (z : Z) :
    Algebra (V.residueField (g z)) (Z.residueField z) :=
  (g.residueFieldMap z).hom.toAlgebra

/-- Residue-field extensions of finite morphisms are finite as modules. -/
instance moduleFinite_residueField_of_isFinite {Z V : Scheme.{u}}
    (g : Z ⟶ V) [IsFinite g] (z : Z) :
    Module.Finite (V.residueField (g z)) (Z.residueField z) :=
  sorry

/-- Residue-field extensions of finite morphisms are algebraic. -/
instance isAlgebraic_residueField_of_isFinite {Z V : Scheme.{u}}
    (g : Z ⟶ V) [IsFinite g] (z : Z) :
    Algebra.IsAlgebraic (V.residueField (g z)) (Z.residueField z) :=
  Algebra.IsAlgebraic.of_finite _ _

/-- The source field of a geometric point is algebraically closed. -/
instance isAlgClosed_geometricPoint (s : GeometricPoint Y) : IsAlgClosed s.K :=
  s.isAlgClosed

/-- Classical decidable equality on same-field geometric points over `ybar`. -/
noncomputable instance (priority := low) decidableEq_over :
    DecidableEq (Over f ybar) :=
  Classical.decEq _

/-- The pairing lift of a geometric point of `X` over `ȳ` with a lift of `ȳ` to
an étale `Y`-scheme, as a morphism to `X_V`. -/
def pairingSchemeHom {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (x : Over f ybar) :
    Spec (.of ybar.K) ⟶ baseChangeScheme f V :=
  pullback.lift v.left x.toScheme ((CategoryTheory.Over.w v).trans x.fac.symm)

/-- The pairing lift of a geometric point of `X` over `ȳ` with a lift of `ȳ` to
an étale `Y`-scheme, as a point of `X_V`. -/
def pairingPoint {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (x : Over f ybar) : baseChangeScheme f V :=
  pairingSchemeHom f ybar v x (default : Spec (.of ybar.K))

/-- The structure morphism of the reduced induced scheme of an admissible
support over an étale `Y`-scheme. -/
abbrev Admissible.toBase {V : Y.Etale} (A : Admissible f V) :
    LocallyClosedReduction.scheme A.subset ⟶ V.left :=
  LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V

/-- Unfolding the structure morphism of an admissible support. -/
theorem Admissible.toBase_eq {V : Y.Etale} (A : Admissible f V) :
    Admissible.toBase f A =
      LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V :=
  sorry

/-- The reduced induced scheme of an admissible support is finite over the étale
base. -/
instance Admissible.instIsFinite_toBase {V : Y.Etale} (A : Admissible f V) :
    IsFinite (Admissible.toBase f A) :=
  A.toBase_isFinite


/-- The point recorded by `SpecToEquivOfField` is the image of the unique point
of `Spec K`. -/
def specToEquivOfField_fst_eq_apply {K : Type u} [Field K] {S : Scheme.{u}}
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
def supportBaseAlgebra {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K))) :
    Algebra (V.left.residueField (Admissible.toBase f A z)) ybar.K :=
  ((V.left.residueFieldCongr
        (hz.trans (specToEquivOfField_fst_eq_apply v.left).symm)).hom ≫
      (SpecToEquivOfField ybar.K V.left v.left).2).hom.toAlgebra

/-- The algebra structure of `supportBaseAlgebra` is the residue-field map of
the geometric lift, transported along the fibre equality. -/
theorem supportBaseAlgebra_eq {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K))) :
    supportBaseAlgebra f ybar v A z hz =
      ((V.left.residueFieldCongr
            (hz.trans (specToEquivOfField_fst_eq_apply v.left).symm)).hom ≫
          (SpecToEquivOfField ybar.K V.left v.left).2).hom.toAlgebra :=
  rfl

/-- Residue-field extensions of finite morphisms have finitely many algebra maps
into a field. -/
theorem finite_algHom_residueField {Z V : Scheme.{u}} (g : Z ⟶ V) [IsFinite g]
    (z : Z) {K : Type u} [Field K]
    (alg : Algebra (V.residueField (g z)) K) :
    Finite (@AlgHom (V.residueField (g z)) (Z.residueField z) K _ _ _
      (algebra_residueField g z) alg) :=
  sorry

/-- Algebra maps `κ(z) →ₐ[κ(v)] ȳ.K` at a fibre point of an admissible support. -/
abbrev supportResidueAlgHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K))) :
    Type u :=
  @AlgHom
    (V.left.residueField (Admissible.toBase f A z))
    ((LocallyClosedReduction.scheme A.subset).residueField z)
    ybar.K _ _ _
    (algebra_residueField (Admissible.toBase f A) z)
    (supportBaseAlgebra f ybar v A z hz)

/-- There are only finitely many `κ(v)`-algebra maps from `κ(z)` into `ȳ.K`. -/
theorem finite_supportResidueAlgHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K))) :
    Finite (supportResidueAlgHom f ybar v A z hz) :=
  finite_algHom_residueField (Admissible.toBase f A) z
    (supportBaseAlgebra f ybar v A z hz)

/-- The finite set of `κ(v)`-algebra maps from `κ(z)` into `ȳ.K`. -/
def supportResidueAlgHomFinset {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K))) :
    Finset (supportResidueAlgHom f ybar v A z hz) :=
  (Set.finite_univ_iff.mpr (finite_supportResidueAlgHom f ybar v A z hz)).toFinset

/-- The underlying ring homomorphism of a fibrewise residue-field algebra map. -/
def supportResidueRingHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K)))
    (φ : supportResidueAlgHom f ybar v A z hz) :
    (LocallyClosedReduction.scheme A.subset).residueField z →+* ybar.K :=
  @AlgHom.toRingHom
    (V.left.residueField (Admissible.toBase f A z))
    ((LocallyClosedReduction.scheme A.subset).residueField z)
    ybar.K _ _ _
    (algebra_residueField (Admissible.toBase f A) z)
    (supportBaseAlgebra f ybar v A z hz) φ

/-- The `CommRingCat` morphism associated to a fibrewise residue-field algebra
map. -/
def supportResidueCommRingHom {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K)))
    (φ : supportResidueAlgHom f ybar v A z hz) :
    (LocallyClosedReduction.scheme A.subset).residueField z ⟶ .of ybar.K :=
  CommRingCat.ofHom (supportResidueRingHom f ybar v A z hz φ)

/-- The geometric point of `X` over `ȳ` associated to a `κ(v)`-algebra map from
the residue field of a fibre point of an admissible support. -/
def overOfSupportPoint {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K)))
    (φ : supportResidueAlgHom f ybar v A z hz) :
    Over f ybar :=
  Over.of f ybar
    (Spec.map (supportResidueCommRingHom f ybar v A z hz φ) ≫
        (LocallyClosedReduction.scheme A.subset).fromSpecResidueField z ≫
          LocallyClosedReduction.ι A.subset ≫ baseChangeToSource f V)
    (by sorry)

/-- The scheme morphism of `overOfSupportPoint` is `Spec` of the given
`κ(v)`-algebra map. -/
theorem overOfSupportPoint_toScheme {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    (z : LocallyClosedReduction.scheme A.subset)
    (hz : Admissible.toBase f A z = v.left (default : Spec (.of ybar.K)))
    (φ : supportResidueAlgHom f ybar v A z hz) :
    (overOfSupportPoint f ybar v A z hz φ).toScheme =
      Spec.map (supportResidueCommRingHom f ybar v A z hz φ) ≫
        (LocallyClosedReduction.scheme A.subset).fromSpecResidueField z ≫
          LocallyClosedReduction.ι A.subset ≫ baseChangeToSource f V :=
  rfl

/-- The finite set of geometric points of `X` over `ȳ` lying on an admissible
support in the fibre of a lift of `ȳ`, obtained by taking every `κ(v)`-algebra
map from the residue field of each scheme point of the fibre. -/
def supportOverFinset {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) : Finset (Over f ybar) :=
  let y0 := v.left (default : Spec (.of ybar.K))
  let hfin := (Admissible.toBase f A).finite_preimage_singleton y0
  hfin.toFinset.attach.biUnion fun z ↦
    let hz : Admissible.toBase f A z.1 = y0 :=
      Set.mem_singleton_iff.mp (Set.mem_preimage.mp (hfin.mem_toFinset.mp z.2))
    (supportResidueAlgHomFinset f ybar v A z.1 hz).image fun ψ ↦
      overOfSupportPoint f ybar v A z.1 hz ψ

/-- Geometric points in `supportOverFinset` are those whose pairing with `v̄`
lies on the admissible support. -/
theorem mem_supportOverFinset_iff {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    (x : Over f ybar) :
    x ∈ supportOverFinset f ybar v A ↔
      pairingPoint f ybar v x ∈ (A.subset : Set (baseChangeScheme f V)) :=
  sorry

/-- Membership in `supportOverFinset` implies that the pairing lands in the
ambient open of the admissible support. -/
theorem supportOverFinset_mem_ambient {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    {x : Over f ybar} (hx : x ∈ supportOverFinset f ybar v A) :
    pairingPoint f ybar v x ∈ (A.ambient : Set _) :=
  sorry

/-- The étale `X`-scheme underlying the ambient open of an admissible support. -/
def ambientEtale {V : Y.Etale} (A : Admissible f V) : X.Etale :=
  Etale.mk (Scheme.Opens.ι A.ambient ≫ baseChangeToSource f V)

/-- The pairing morphism of a geometric point in the ambient open factors through
that open immersion. -/
theorem pairingSchemeHom_range_subset_ambient {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    (x : Over f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    Set.range (pairingSchemeHom f ybar v x) ⊆ Set.range A.ambient.ι :=
  sorry

/-- Open-immersion lift of a pairing into the ambient open of an admissible
support. -/
def ambientOpenLift {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) (x : Over f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    Spec (.of ybar.K) ⟶ A.ambient.toScheme :=
  (A.ambient.instIsOpenImmersionι).lift A.ambient.ι
    (pairingSchemeHom f ybar v x)
    (pairingSchemeHom_range_subset_ambient f ybar v A x hx)

/-- The lift of a geometric point of `X` over `ȳ` to the ambient open of an
admissible support, when the pairing lands in that open. -/
def ambientFiberLift {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) (x : Over f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    (toSmallEtalePoint x.toGeometricPoint).fiber.obj (ambientEtale f A) :=
  CategoryTheory.Over.homMk (ambientOpenLift f ybar v A x hx) sorry

/-- Germ of an ambient supported section at a geometric point of `X` over `ȳ`. -/
def supportGerm (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (v : (toSmallEtalePoint ybar).fiber.obj V) (A : Admissible f V)
    (x : Over f ybar)
    (hx : pairingPoint f ybar v x ∈ (A.ambient : Set _)) :
    sections f F A ⟶
      (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        (toSmallEtalePoint x.toGeometricPoint).toPresheafFiber
          (ambientEtale f A) (ambientFiberLift f ybar v A x hx) F.1 σ.1
      map_zero' := sorry
      map_add' := sorry }

/-- The map sending a supported section on `X_V` to the finite sum of its germs
at geometric points of the support over `ȳ`. -/
def supportToCoproduct (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V)
    (A : Admissible f V) :
    sections f F A ⟶ (abelianStalkCoproduct f ybar).obj F :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        ∑ x ∈ (supportOverFinset f ybar v A).attach,
          (Sigma.ι (fun x : Over f ybar ↦
              (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F) x.1)
            (supportGerm f ybar F v A x.1
              (supportOverFinset_mem_ambient f ybar v A x.2) σ)
      map_zero' := sorry
      map_add' := sorry }

/-- Cocone of germ-sum maps from the finite-support diagram at an étale
neighbourhood of `ȳ`. -/
def supportToCoproductCocone (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (v : (toSmallEtalePoint ybar).fiber.obj V) :
    Cocone (diagram f F V) :=
  Cocone.mk ((abelianStalkCoproduct f ybar).obj F)
    { app := fun A ↦ supportToCoproduct f ybar F v A
      naturality := sorry }

/-- The comparison out of `f_{p!} F(V)` obtained by summing germs of supported
sections. -/
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

/-- Isolatedness of a fibre point of an étale neighbourhood composed with `f`. -/
theorem isOpen_asFiber_etale_comp (U : X.Etale) (u : U.left) :
    IsOpen ({(U.hom ≫ f).asFiber u} : Set ((U.hom ≫ f).fiber ((U.hom ≫ f) u))) :=
  sorry

/-- The image of a geometric lift of `x̄` under `U ⟶ Y` is the image of `ȳ`. -/
theorem finiteNeighborhood_comp_image_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (U.hom ≫ f) (u.left (default : Spec (.of ybar.K))) = ybar.image :=
  sorry

/-- Lemma 37.41.3 applied to the image of an étale neighbourhood of `x̄`. -/
@[irreducible]
def finiteNeighborhood (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  exists_finiteOpen_etaleNeighborhoods_purelyInseparable (U.hom ≫ f)
    ybar.image 1 (fun _ ↦ u.left (default : Spec (.of ybar.K)))
    (fun _ ↦ finiteNeighborhood_comp_image_eq f ybar x U u)
    (fun {a b} _ ↦ Subsingleton.elim a b)
    (fun _ ↦ isOpen_asFiber_etale_comp f U
      (u.left (default : Spec (.of ybar.K))))

/-- Ordinary étale neighbourhood of the image of `ȳ` supplied by Lemma 37.41.3. -/
def finiteNeighborhoodOrdinary (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Scheme.EtaleNeighborhood Y ybar.image :=
  Classical.choose (finiteNeighborhood f ybar x U u)

/-- The étale `Y`-scheme underlying the ordinary neighbourhood of Lemma 37.41.3. -/
def finiteNeighborhoodBaseEtale (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) : Y.Etale :=
  (finiteNeighborhoodOrdinary f ybar x U u).toEtale

/-- Existence of a geometric lift of `ȳ` to the Lemma 37.41.3 neighbourhood. -/
@[irreducible]
def finiteNeighborhoodBaseLiftExists (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  exists_fac_of_etale_of_isSepClosed
    (finiteNeighborhoodBaseEtale f ybar x U u).hom ybar.hom
    (finiteNeighborhoodOrdinary f ybar x U u).point
    (EtaleNeighborhood.map_point _)

/-- Geometric lift of `ȳ` to the étale neighbourhood produced by Lemma 37.41.3,
as a scheme morphism. -/
def finiteNeighborhoodBaseLiftScheme (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Spec (.of ybar.K) ⟶ (finiteNeighborhoodBaseEtale f ybar x U u).left :=
  Classical.choose (finiteNeighborhoodBaseLiftExists f ybar x U u)

/-- The chosen lift of `ȳ` lies over `ȳ`. -/
theorem finiteNeighborhoodBaseLiftScheme_fac (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteNeighborhoodBaseLiftScheme f ybar x U u ≫
        (finiteNeighborhoodBaseEtale f ybar x U u).hom =
      ybar.hom :=
  (Classical.choose_spec (finiteNeighborhoodBaseLiftExists f ybar x U u)).1

/-- The chosen lift of `ȳ` hits the distinguished point of the neighbourhood. -/
theorem finiteNeighborhoodBaseLiftScheme_apply (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteNeighborhoodBaseLiftScheme f ybar x U u default =
      (finiteNeighborhoodOrdinary f ybar x U u).point :=
  (Classical.choose_spec (finiteNeighborhoodBaseLiftExists f ybar x U u)).2

/-- Geometric lift of `ȳ` to the étale neighbourhood produced by Lemma 37.41.3. -/
def finiteNeighborhoodBaseLift (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (toSmallEtalePoint ybar).fiber.obj
      (finiteNeighborhoodBaseEtale f ybar x U u) :=
  CategoryTheory.Over.homMk (finiteNeighborhoodBaseLiftScheme f ybar x U u)
    (finiteNeighborhoodBaseLiftScheme_fac f ybar x U u)

/-- Compatibility of the pairing lift into `U ×_Y V`. -/
theorem finiteNeighborhoodPullbackLift_fac (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    u.left ≫ U.hom ≫ f =
      finiteNeighborhoodBaseLiftScheme f ybar x U u ≫
        (finiteNeighborhoodBaseEtale f ybar x U u).hom :=
  sorry

/-- The pairing morphism of the lift of `x̄` with the Lemma 37.41.3 neighbourhood. -/
def finiteNeighborhoodPullbackLift (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Spec (.of ybar.K) ⟶
      pullback (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom :=
  pullback.lift u.left (finiteNeighborhoodBaseLiftScheme f ybar x U u)
    (finiteNeighborhoodPullbackLift_fac f ybar x U u)

/-- The pairing of the lift of `x̄` with the Lemma 37.41.3 neighbourhood. -/
def finiteNeighborhoodPullbackPoint (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  finiteNeighborhoodPullbackLift f ybar x U u (default : Spec (.of ybar.K))

/-- The pairing point is the evaluation of the pairing morphism at the unique
point of `Spec k`. -/
theorem finiteNeighborhoodPullbackPoint_apply (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteNeighborhoodPullbackPoint f ybar x U u =
      finiteNeighborhoodPullbackLift f ybar x U u
        (default : Spec (.of ybar.K)) :=
  rfl

/-- Multiplicities `m_i` from Lemma 37.41.3 at the unique selected point. -/
@[irreducible]
def finiteNeighborhoodOrdinary_spec (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhood f ybar x U u)

/-- Multiplicities `m_i` from Lemma 37.41.3 at the unique selected point. -/
def finiteNeighborhoodMultiplicity (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) : Fin 1 → ℕ :=
  Classical.choose (finiteNeighborhoodOrdinary_spec f ybar x U u)

/-- The chosen multiplicities retain the remaining finite-open witnesses. -/
@[irreducible]
def finiteNeighborhoodMultiplicity_spec (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhoodOrdinary_spec f ybar x U u)

/-- The Lemma 37.41.3 family of finite opens over the unique selected point. -/
def finiteNeighborhoodFamily (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    ∀ i, Fin (finiteNeighborhoodMultiplicity f ybar x U u i) →
      (pullback (U.hom ≫ f)
        (finiteNeighborhoodBaseEtale f ybar x U u).hom).Opens :=
  Classical.choose (finiteNeighborhoodMultiplicity_spec f ybar x U u)

/-- The chosen open family retains its selected-point witnesses. -/
@[irreducible]
def finiteNeighborhoodFamily_spec (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhoodMultiplicity_spec f ybar x U u)

/-- Selected fibre points of the Lemma 37.41.3 family. -/
def finiteNeighborhoodSelected (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    ∀ i (j : Fin (finiteNeighborhoodMultiplicity f ybar x U u i)),
      finiteNeighborhoodFamily f ybar x U u i j :=
  Classical.choose (finiteNeighborhoodFamily_spec f ybar x U u)

/-- The pairing of `x̄` with the Lemma 37.41.3 neighbourhood lies over the
distinguished point of that neighbourhood. -/
theorem finiteNeighborhoodPullbackPoint_snd (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (pullback.snd (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom)
        (finiteNeighborhoodPullbackPoint f ybar x U u) =
      (finiteNeighborhoodOrdinary f ybar x U u).point :=
  sorry

/-- The pairing of `x̄` with the Lemma 37.41.3 neighbourhood maps to the original
lift of `x̄`. -/
theorem finiteNeighborhoodPullbackPoint_fst (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (pullback.fst (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom)
        (finiteNeighborhoodPullbackPoint f ybar x U u) =
      u.left (default : Spec (.of ybar.K)) :=
  sorry

/-- Inner existence data of Lemma 37.41.3 after unpacking the neighbourhood,
multiplicities, opens, and selected points. -/
@[irreducible]
def finiteNeighborhoodInner (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  Classical.choose_spec (finiteNeighborhoodFamily_spec f ybar x U u)

/-- Finiteness of each Lemma 37.41.3 component over the étale neighbourhood,
extracted from the existential package of Lemma 37.41.3. -/
theorem finiteNeighborhoodFamily_isFinite (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    ∀ i j, IsFinite
      ((finiteNeighborhoodFamily f ybar x U u i j).ι ≫
        pullback.snd (U.hom ≫ f)
          (finiteNeighborhoodBaseEtale f ybar x U u).hom) :=
  Classical.choose (finiteNeighborhoodInner f ybar x U u)

/-- Exhaustiveness of the Lemma 37.41.3 family over the unique selected point. -/
@[irreducible]
def finiteNeighborhoodExhaust (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  Classical.choose_spec <|
    Classical.choose_spec <|
      Classical.choose_spec <|
        Classical.choose_spec <|
          Classical.choose_spec <|
            Classical.choose_spec <|
              Classical.choose_spec (finiteNeighborhoodInner f ybar x U u)

/-- Unfolding the multiplicity function of Lemma 37.41.3. -/
theorem finiteNeighborhoodMultiplicity_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteNeighborhoodMultiplicity f ybar x U u =
      Classical.choose
        (Classical.choose_spec (finiteNeighborhood f ybar x U u)) :=
  rfl

/-- The unique Lemma 37.41.3 component containing the pairing of `x̄`. -/
def finiteNeighborhoodIndex (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Fin (finiteNeighborhoodMultiplicity f ybar x U u (0 : Fin 1)) :=
  Classical.choose
    (finiteNeighborhoodExhaust f ybar x U u (0 : Fin 1)
      (finiteNeighborhoodPullbackPoint f ybar x U u)
      (finiteNeighborhoodPullbackPoint_snd f ybar x U u)
      (finiteNeighborhoodPullbackPoint_fst f ybar x U u))

/-- Finite open of `U ×_Y V` supplied by Lemma 37.41.3 through the pairing of
`x̄`, namely the unique family component containing that pairing. -/
def finiteNeighborhoodOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (pullback (U.hom ≫ f)
      (finiteNeighborhoodBaseEtale f ybar x U u).hom).Opens :=
  finiteNeighborhoodFamily f ybar x U u (0 : Fin 1)
    (finiteNeighborhoodIndex f ybar x U u)

/-- The selected open is the unique Lemma 37.41.3 component through the pairing
of `x̄`. -/
theorem finiteNeighborhoodOpen_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteNeighborhoodOpen f ybar x U u =
      finiteNeighborhoodFamily f ybar x U u (0 : Fin 1)
        (finiteNeighborhoodIndex f ybar x U u) :=
  rfl

/-- The selected Lemma 37.41.3 open is finite over the étale neighbourhood. -/
instance finiteNeighborhoodOpen_isFinite (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    IsFinite
      ((finiteNeighborhoodOpen f ybar x U u).ι ≫
        pullback.snd (U.hom ≫ f)
          (finiteNeighborhoodBaseEtale f ybar x U u).hom) :=
  finiteNeighborhoodFamily_isFinite f ybar x U u (0 : Fin 1)
    (finiteNeighborhoodIndex f ybar x U u)

/-- The pairing of `x̄` is the selected fibre point of its Lemma 37.41.3
component. -/
theorem finiteNeighborhoodIndex_spec (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteNeighborhoodPullbackPoint f ybar x U u =
      (finiteNeighborhoodFamily f ybar x U u (0 : Fin 1)
          (finiteNeighborhoodIndex f ybar x U u)).ι
        (finiteNeighborhoodSelected f ybar x U u (0 : Fin 1)
          (finiteNeighborhoodIndex f ybar x U u)) :=
  sorry

/-- Selected fibre point of the Lemma 37.41.3 open over `ȳ`. -/
def finiteNeighborhoodPoint (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteNeighborhoodOpen f ybar x U u :=
  ⟨finiteNeighborhoodPullbackPoint f ybar x U u, sorry⟩

/-- The selected Lemma 37.41.3 component is finite over the base, has a unique
geometric point over `v̄`, and that point maps to the original lift of `x̄`. -/
theorem finiteNeighborhoodOpen_spec (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
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

/-- The morphism from the Lemma 37.41.3 open into the base change `X_V`. -/
def finiteNeighborhoodToBaseChange (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
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

/-- The morphism from the Lemma 37.41.3 open to the original étale neighbourhood
of `x̄`. -/
def finiteNeighborhoodToU (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (finiteNeighborhoodOpen f ybar x U u).toScheme ⟶ U.left :=
  (finiteNeighborhoodOpen f ybar x U u).ι ≫
    pullback.fst (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom

/-- Existence of an affine open of `X_V` containing the image of the Lemma
37.41.3 pairing. -/
theorem exists_sourceAmbientOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    ∃ W' : (baseChangeScheme f
        (finiteNeighborhoodBaseEtale f ybar x U u)).Opens,
      IsAffineOpen W' ∧
        finiteNeighborhoodToBaseChange f ybar x U u
            (finiteNeighborhoodPoint f ybar x U u) ∈ W' :=
  sorry

/-- Affine open `W'` of `X_V` containing the image of the Lemma 37.41.3 pairing. -/
def sourceAmbientOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (baseChangeScheme f (finiteNeighborhoodBaseEtale f ybar x U u)).Opens :=
  Classical.choose (exists_sourceAmbientOpen f ybar x U u)

/-- The chosen open of `X_V` is affine and contains the image of the pairing. -/
theorem sourceAmbientOpen_spec (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    IsAffineOpen (sourceAmbientOpen f ybar x U u) ∧
      finiteNeighborhoodToBaseChange f ybar x U u
          (finiteNeighborhoodPoint f ybar x U u) ∈
        sourceAmbientOpen f ybar x U u :=
  Classical.choose_spec (exists_sourceAmbientOpen f ybar x U u)

/-- Points of the Lemma 37.41.3 neighbourhood over which some point of the finite
open fails to land in `W'`. -/
def finiteNeighborhoodEscape (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Set (finiteNeighborhoodOrdinary f ybar x U u).toEtale.left :=
  ((finiteNeighborhoodOpen f ybar x U u).ι ≫
      pullback.snd (U.hom ≫ f)
        (finiteNeighborhoodBaseEtale f ybar x U u).hom) ''
    (finiteNeighborhoodToBaseChange f ybar x U u ⁻¹'
      (sourceAmbientOpen f ybar x U u : Set _)ᶜ)

/-- Open of the Lemma 37.41.3 neighbourhood over which the finite open lands in
the chosen ambient open of `X_V`. -/
def shrunkBaseOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (finiteNeighborhoodOrdinary f ybar x U u).toEtale.left.Opens :=
  ⟨(finiteNeighborhoodEscape f ybar x U u)ᶜ, sorry⟩

/-- The distinguished point of the Lemma 37.41.3 neighbourhood survives the
shrinking. -/
theorem shrunkBaseOpen_mem_point (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (finiteNeighborhoodOrdinary f ybar x U u).point ∈
      shrunkBaseOpen f ybar x U u :=
  sorry

/-- The shrunk neighbourhood remains étale over `Y`. -/
instance shrunkBase_isEtale (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Etale
      ((shrunkBaseOpen f ybar x U u).ι ≫
        (finiteNeighborhoodBaseEtale f ybar x U u).hom) :=
  sorry

/-- Étale neighbourhood of `ȳ` obtained by shrinking the Lemma 37.41.3
neighbourhood so that the finite open lands in `W'`. -/
def landingBaseEtale (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) : Y.Etale :=
  MorphismProperty.Over.mk _
    ((shrunkBaseOpen f ybar x U u).ι ≫
      (finiteNeighborhoodBaseEtale f ybar x U u).hom)
    (shrunkBase_isEtale f ybar x U u)

/-- Open immersion of the shrunk neighbourhood into the Lemma 37.41.3
neighbourhood. -/
def shrunkBaseEtaleHom (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    landingBaseEtale f ybar x U u ⟶
      finiteNeighborhoodBaseEtale f ybar x U u :=
  MorphismProperty.Over.homMk (shrunkBaseOpen f ybar x U u).ι sorry

/-- Comparison of base changes `X_{V'} ⟶ X_V` along the shrinking. -/
def shrunkBaseChangeMap (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    baseChangeScheme f (landingBaseEtale f ybar x U u) ⟶
      baseChangeScheme f (finiteNeighborhoodBaseEtale f ybar x U u) :=
  ((smallEtalePullback f).map (shrunkBaseEtaleHom f ybar x U u)).left

/-- Comparison of fibre products `U ×_Y V' ⟶ U ×_Y V` along the shrinking. -/
def shrunkPullbackMap (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom ⟶
      pullback (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom :=
  pullback.map (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom
    (U.hom ≫ f) (finiteNeighborhoodBaseEtale f ybar x U u).hom
    (𝟙 _) (shrunkBaseOpen f ybar x U u).ι (𝟙 _) rfl rfl

/-- The lift of `ȳ` to the Lemma 37.41.3 neighbourhood factors through the
shrunk open. -/
theorem finiteNeighborhoodBaseLiftScheme_range_subset_shrunk
    (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Set.range (finiteNeighborhoodBaseLiftScheme f ybar x U u) ⊆
      Set.range (shrunkBaseOpen f ybar x U u).ι :=
  sorry

/-- Geometric lift of `ȳ` to the shrunk neighbourhood, as a scheme morphism. -/
def landingBaseLiftScheme (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Spec (.of ybar.K) ⟶ (landingBaseEtale f ybar x U u).left :=
  (shrunkBaseOpen f ybar x U u).instIsOpenImmersionι.lift
    (shrunkBaseOpen f ybar x U u).ι
    (finiteNeighborhoodBaseLiftScheme f ybar x U u)
    (finiteNeighborhoodBaseLiftScheme_range_subset_shrunk f ybar x U u)

/-- The chosen lift of `ȳ` to the shrunk neighbourhood lies over `ȳ`. -/
theorem landingBaseLiftScheme_fac (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    landingBaseLiftScheme f ybar x U u ≫ (landingBaseEtale f ybar x U u).hom =
      ybar.hom :=
  sorry

/-- Geometric lift of `ȳ` to the shrunk étale neighbourhood. -/
def landingBaseLift (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (toSmallEtalePoint ybar).fiber.obj (landingBaseEtale f ybar x U u) :=
  CategoryTheory.Over.homMk (landingBaseLiftScheme f ybar x U u)
    (landingBaseLiftScheme_fac f ybar x U u)

/-- The Lemma 37.41.3 finite open, pulled back to the shrunk neighbourhood. -/
def landingFiniteOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom).Opens :=
  shrunkPullbackMap f ybar x U u ⁻¹ᵁ finiteNeighborhoodOpen f ybar x U u

/-- The once-shrunk finite open is the pullback of the Lemma 37.41.3 open. -/
theorem landingFiniteOpen_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    landingFiniteOpen f ybar x U u =
      shrunkPullbackMap f ybar x U u ⁻¹ᵁ
        finiteNeighborhoodOpen f ybar x U u :=
  rfl

/-- The once-shrunk Lemma 37.41.3 open remains finite over the shrunk base, as a
base change of `finiteNeighborhoodOpen_isFinite`. -/
instance landingFiniteOpen_isFinite (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    IsFinite
      ((landingFiniteOpen f ybar x U u).ι ≫
        pullback.snd (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom) :=
  sorry

/-- The affine open `W'` of `X_V`, pulled back to `X_{V'}`. -/
def sourceAmbientShrunk (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (baseChangeScheme f (landingBaseEtale f ybar x U u)).Opens :=
  shrunkBaseChangeMap f ybar x U u ⁻¹ᵁ sourceAmbientOpen f ybar x U u

/-- The morphism from the pulled-back finite open into `X_{V'}`. -/
def landingFiniteToBaseChange (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
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
theorem landingFiniteToBaseChange_range_subset_ambient
    (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Set.range (landingFiniteToBaseChange f ybar x U u) ⊆
      Set.range (sourceAmbientShrunk f ybar x U u).ι :=
  sorry

/-- The morphism from the Lemma 37.41.3 open to the original étale neighbourhood
of `x̄`, after shrinking. -/
def landingFiniteToU (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (landingFiniteOpen f ybar x U u).toScheme ⟶ U.left :=
  (landingFiniteOpen f ybar x U u).ι ≫
    pullback.fst (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom

/-- Finite étale map from the shrunk Lemma 37.41.3 open into `W' ⊂ X_{V'}`. -/
def finiteToAmbient (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (landingFiniteOpen f ybar x U u).toScheme ⟶
      (sourceAmbientShrunk f ybar x U u).toScheme :=
  (sourceAmbientShrunk f ybar x U u).instIsOpenImmersionι.lift
    (sourceAmbientShrunk f ybar x U u).ι
    (landingFiniteToBaseChange f ybar x U u)
    (landingFiniteToBaseChange_range_subset_ambient f ybar x U u)

/-- After shrinking, the map into `W'` is finite. -/
instance finiteToAmbient_isFinite (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    IsFinite (finiteToAmbient f ybar x U u) :=
  sorry

/-- After shrinking, the map into `W'` is étale. -/
instance finiteToAmbient_isEtale (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Etale (finiteToAmbient f ybar x U u) :=
  sorry

/-- Compatibility of the pairing lift into `U ×_Y V'` after shrinking. -/
theorem landingPullbackLift_fac (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    u.left ≫ U.hom ≫ f =
      landingBaseLiftScheme f ybar x U u ≫
        (landingBaseEtale f ybar x U u).hom :=
  sorry

/-- The pairing morphism of the lift of `x̄` with the shrunk neighbourhood. -/
def landingPullbackLift (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Spec (.of ybar.K) ⟶
      pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom :=
  pullback.lift u.left (landingBaseLiftScheme f ybar x U u)
    (landingPullbackLift_fac f ybar x U u)

/-- The pairing of `x̄`, as a point of the shrunk finite open. -/
def finiteToAmbientPoint (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    landingFiniteOpen f ybar x U u :=
  ⟨landingPullbackLift f ybar x U u (default : Spec (.of ybar.K)), sorry⟩

/-- Image of the pairing in the shrunk ambient open `W'`. -/
def ambientImagePoint (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    sourceAmbientShrunk f ybar x U u :=
  finiteToAmbient f ybar x U u (finiteToAmbientPoint f ybar x U u)

/-- After shrinking, the finite étale map into `W'` has a unique point over the
image of the pairing. -/
theorem finiteToAmbient_uniqueFiber (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    finiteToAmbient f ybar x U u ⁻¹'
        {ambientImagePoint f ybar x U u} =
      {finiteToAmbientPoint f ybar x U u} :=
  sorry

/-- The residue-field extension of the finite étale map into `W'` at the pairing
is purely inseparable. -/
theorem finiteToAmbient_purelyInseparable (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    ((Scheme.residueFieldCongr rfl).inv ≫
        (finiteToAmbient f ybar x U u).residueFieldMap
          (finiteToAmbientPoint f ybar x U u)).hom.IsPurelyInseparable :=
  sorry

/-- Lemma 41.14.2 applied to the finite étale map from the shrunk Lemma 37.41.3
open into `W'`. -/
def isoNeighborhoodExists (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :=
  AlgebraicGeometry.Etale.exists_isIso_morphismRestrict
    (finiteToAmbient f ybar x U u)
    (ambientImagePoint f ybar x U u)
    (finiteToAmbientPoint f ybar x U u) rfl
    (finiteToAmbient_uniqueFiber f ybar x U u)
    (finiteToAmbient_purelyInseparable f ybar x U u)

/-- Open of `W'` along which Lemma 41.14.2 makes the finite étale map an
isomorphism. -/
def isoNeighborhoodOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (sourceAmbientShrunk f ybar x U u).toScheme.Opens :=
  Classical.choose (isoNeighborhoodExists f ybar x U u)

/-- The chosen open of `W'` contains the image of the pairing and makes the
finite étale map an isomorphism. -/
theorem isoNeighborhoodOpen_spec (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    ambientImagePoint f ybar x U u ∈ isoNeighborhoodOpen f ybar x U u ∧
      IsIso
        (finiteToAmbient f ybar x U u ∣_
          isoNeighborhoodOpen f ybar x U u) :=
  Classical.choose_spec (isoNeighborhoodExists f ybar x U u)

/-- Image of the Lemma 41.14.2 open in `X_{V'}`, as an open of the once-shrunk
base change. -/
def landingIsoAmbientOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (baseChangeScheme f (landingBaseEtale f ybar x U u)).Opens :=
  (sourceAmbientShrunk f ybar x U u).ι ''ᵁ
    isoNeighborhoodOpen f ybar x U u

/-- Unfolding the image of the Lemma 41.14.2 open in `X_{V'}`. -/
theorem landingIsoAmbientOpen_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    landingIsoAmbientOpen f ybar x U u =
      (sourceAmbientShrunk f ybar x U u).ι ''ᵁ
        isoNeighborhoodOpen f ybar x U u :=
  rfl

/-- Points of the once-shrunk neighbourhood over which some point of the finite
open fails to land in the Lemma 41.14.2 isomorphism locus. -/
def isoNeighborhoodEscape (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Set (landingBaseEtale f ybar x U u).left :=
  ((landingFiniteOpen f ybar x U u).ι ≫
      pullback.snd (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom) ''
    (finiteToAmbient f ybar x U u ⁻¹'
      (isoNeighborhoodOpen f ybar x U u : Set _)ᶜ)

/-- Unfolding the escape set of the Lemma 41.14.2 locus. -/
theorem isoNeighborhoodEscape_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    isoNeighborhoodEscape f ybar x U u =
      ((landingFiniteOpen f ybar x U u).ι ≫
          pullback.snd (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom) ''
        (finiteToAmbient f ybar x U u ⁻¹'
          (isoNeighborhoodOpen f ybar x U u : Set _)ᶜ) :=
  rfl

/-- Open of the once-shrunk neighbourhood obtained by deleting the closed image
of the finite open outside the Lemma 41.14.2 isomorphism locus. -/
def isoBaseOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (landingBaseEtale f ybar x U u).left.Opens :=
  ⟨(isoNeighborhoodEscape f ybar x U u)ᶜ, sorry⟩

/-- The lift of `ȳ` to the once-shrunk neighbourhood survives the second
shrinking. -/
theorem isoBaseOpen_mem_point (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    landingBaseLiftScheme f ybar x U u default ∈ isoBaseOpen f ybar x U u :=
  sorry

/-- The twice-shrunk neighbourhood remains étale over `Y`. -/
instance isoBase_isEtale (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Etale
      ((isoBaseOpen f ybar x U u).ι ≫
        (landingBaseEtale f ybar x U u).hom) :=
  sorry

/-- Étale neighbourhood of `ȳ` obtained by shrinking `V` and `W'` until the
finite open maps isomorphically onto the pulled-back isomorphism locus. -/
def inverseBaseEtale (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) : Y.Etale :=
  MorphismProperty.Over.mk _
    ((isoBaseOpen f ybar x U u).ι ≫
      (landingBaseEtale f ybar x U u).hom)
    (isoBase_isEtale f ybar x U u)

/-- Open immersion of the twice-shrunk neighbourhood into the once-shrunk
neighbourhood. -/
def isoBaseEtaleHom (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    inverseBaseEtale f ybar x U u ⟶ landingBaseEtale f ybar x U u :=
  MorphismProperty.Over.homMk (isoBaseOpen f ybar x U u).ι sorry

/-- The underlying scheme morphism of `isoBaseEtaleHom` is the open immersion of
the second shrinking. -/
theorem isoBaseEtaleHom_left (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (isoBaseEtaleHom f ybar x U u).left = (isoBaseOpen f ybar x U u).ι :=
  rfl

/-- Comparison of base changes `X_{V''} ⟶ X_{V'}` along the second shrinking. -/
def isoBaseChangeMap (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    baseChangeScheme f (inverseBaseEtale f ybar x U u) ⟶
      baseChangeScheme f (landingBaseEtale f ybar x U u) :=
  ((smallEtalePullback f).map (isoBaseEtaleHom f ybar x U u)).left

/-- Unfolding the second-shrink base-change comparison. -/
theorem isoBaseChangeMap_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    isoBaseChangeMap f ybar x U u =
      ((smallEtalePullback f).map (isoBaseEtaleHom f ybar x U u)).left :=
  rfl

/-- Comparison of fibre products `U ×_Y V'' ⟶ U ×_Y V'` along the second
shrinking. -/
def isoPullbackMap (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    pullback (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom ⟶
      pullback (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom :=
  pullback.map (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom
    (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom
    (𝟙 _) (isoBaseOpen f ybar x U u).ι (𝟙 _) rfl rfl

/-- Unfolding the second-shrink fibre-product comparison. -/
theorem isoPullbackMap_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    isoPullbackMap f ybar x U u =
      pullback.map (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom
        (U.hom ≫ f) (landingBaseEtale f ybar x U u).hom
        (𝟙 _) (isoBaseOpen f ybar x U u).ι (𝟙 _) rfl rfl :=
  rfl

/-- The lift of `ȳ` to the once-shrunk neighbourhood factors through the second
shrinking. -/
theorem landingBaseLiftScheme_range_subset_iso (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Set.range (landingBaseLiftScheme f ybar x U u) ⊆
      Set.range (isoBaseOpen f ybar x U u).ι :=
  sorry

/-- Geometric lift of `ȳ` to the twice-shrunk neighbourhood, as a scheme
morphism. -/
def inverseBaseLiftScheme (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Spec (.of ybar.K) ⟶ (inverseBaseEtale f ybar x U u).left :=
  (isoBaseOpen f ybar x U u).instIsOpenImmersionι.lift
    (isoBaseOpen f ybar x U u).ι
    (landingBaseLiftScheme f ybar x U u)
    (landingBaseLiftScheme_range_subset_iso f ybar x U u)

/-- The chosen lift of `ȳ` to the twice-shrunk neighbourhood lies over `ȳ`. -/
theorem inverseBaseLiftScheme_fac (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    inverseBaseLiftScheme f ybar x U u ≫ (inverseBaseEtale f ybar x U u).hom =
      ybar.hom :=
  sorry

/-- Geometric lift of `ȳ` to the twice-shrunk étale neighbourhood. -/
def inverseBaseLift (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (toSmallEtalePoint ybar).fiber.obj (inverseBaseEtale f ybar x U u) :=
  CategoryTheory.Over.homMk (inverseBaseLiftScheme f ybar x U u)
    (inverseBaseLiftScheme_fac f ybar x U u)

/-- The Lemma 37.41.3 finite open, pulled back to the twice-shrunk
neighbourhood. -/
def inverseFiniteOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (pullback (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom).Opens :=
  isoPullbackMap f ybar x U u ⁻¹ᵁ landingFiniteOpen f ybar x U u

/-- The twice-shrunk finite open is the pullback of the once-shrunk finite
open. -/
theorem inverseFiniteOpen_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    inverseFiniteOpen f ybar x U u =
      isoPullbackMap f ybar x U u ⁻¹ᵁ landingFiniteOpen f ybar x U u :=
  rfl

/-- The twice-shrunk finite open remains finite over the twice-shrunk base, as a
base change of `landingFiniteOpen_isFinite` and hence of
`finiteNeighborhoodOpen_isFinite`. -/
instance inverseFiniteOpen_isFinite (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    IsFinite
      ((inverseFiniteOpen f ybar x U u).ι ≫
        pullback.snd (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom) :=
  sorry

/-- The Lemma 41.14.2 open of `W'`, pulled back to `X_{V''}`. After the second
shrinking this is the open subscheme of `X_{V''}` isomorphic to the pulled-back
finite open. -/
def inverseAmbientOpen (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (baseChangeScheme f (inverseBaseEtale f ybar x U u)).Opens :=
  isoBaseChangeMap f ybar x U u ⁻¹ᵁ landingIsoAmbientOpen f ybar x U u

/-- The twice-shrunk ambient open is the pullback of the Lemma 41.14.2 image. -/
theorem inverseAmbientOpen_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    inverseAmbientOpen f ybar x U u =
      isoBaseChangeMap f ybar x U u ⁻¹ᵁ
        landingIsoAmbientOpen f ybar x U u :=
  rfl

/-- The morphism from the twice-shrunk finite open into `X_{V''}`. -/
def inverseFiniteToBaseChange (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
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
theorem inverseFiniteToBaseChange_range_subset_ambient
    (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Set.range (inverseFiniteToBaseChange f ybar x U u) ⊆
      Set.range (inverseAmbientOpen f ybar x U u).ι :=
  sorry

/-- The morphism from the twice-shrunk finite open to the original étale
neighbourhood of `x̄`. -/
def inverseFiniteToU (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (inverseFiniteOpen f ybar x U u).toScheme ⟶ U.left :=
  (inverseFiniteOpen f ybar x U u).ι ≫
    pullback.fst (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom

/-- Unfolding the projection of the twice-shrunk finite open to `U`. -/
theorem inverseFiniteToU_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    inverseFiniteToU f ybar x U u =
      (inverseFiniteOpen f ybar x U u).ι ≫
        pullback.fst (U.hom ≫ f) (inverseBaseEtale f ybar x U u).hom :=
  rfl

/-- After the second shrinking, the finite open maps to the pulled-back
isomorphism locus `W' ⊂ X_{V''}`. -/
def inverseFiniteToAmbient (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (inverseFiniteOpen f ybar x U u).toScheme ⟶
      (inverseAmbientOpen f ybar x U u).toScheme :=
  (inverseAmbientOpen f ybar x U u).instIsOpenImmersionι.lift
    (inverseAmbientOpen f ybar x U u).ι
    (inverseFiniteToBaseChange f ybar x U u)
    (inverseFiniteToBaseChange_range_subset_ambient f ybar x U u)

/-- The lift of the twice-shrunk finite open into `W'` recovers the open
immersion into `X_{V''}`. -/
theorem inverseFiniteToAmbient_ι (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    inverseFiniteToAmbient f ybar x U u ≫
        (inverseAmbientOpen f ybar x U u).ι =
      inverseFiniteToBaseChange f ybar x U u :=
  sorry

/-- After shrinking `V` and `W'` a second time, the finite open maps
isomorphically onto the pulled-back `W'`. -/
instance inverseFiniteToAmbient_isIso (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    IsIso (inverseFiniteToAmbient f ybar x U u) :=
  sorry

/-- Scheme morphism from the pulled-back `W'` to the original étale neighbourhood
of `x̄`, via the isomorphism with the twice-shrunk finite open. -/
def inverseAmbientToUScheme (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (inverseAmbientOpen f ybar x U u).toScheme ⟶ U.left :=
  (asIso (inverseFiniteToAmbient f ybar x U u)).inv ≫
    inverseFiniteToU f ybar x U u

/-- Unfolding the transport of sections from `W'` to `U`. -/
theorem inverseAmbientToUScheme_eq (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    inverseAmbientToUScheme f ybar x U u =
      (asIso (inverseFiniteToAmbient f ybar x U u)).inv ≫
        inverseFiniteToU f ybar x U u :=
  rfl

/-- The pulled-back `W'` is étale over `X`. -/
instance inverseAmbient_isEtale (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Etale
      ((inverseAmbientOpen f ybar x U u).ι ≫
        baseChangeToSource f (inverseBaseEtale f ybar x U u)) :=
  sorry

/-- Restriction morphism of small-étale `X`-schemes from the pulled-back `W'` to
the original neighbourhood of `x̄`. -/
def inverseAmbientToU (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    Etale.mk
        ((inverseAmbientOpen f ybar x U u).ι ≫
          baseChangeToSource f (inverseBaseEtale f ybar x U u)) ⟶
      U :=
  MorphismProperty.Over.homMk (inverseAmbientToUScheme f ybar x U u) sorry

/-- The underlying scheme morphism of `inverseAmbientToU` is the transport along
`W ≅ W'`. -/
theorem inverseAmbientToU_left (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    (inverseAmbientToU f ybar x U u).left =
      inverseAmbientToUScheme f ybar x U u :=
  sorry

/-- The pulled-back `W'` is finite over the twice-shrunk neighbourhood, by
transporting `inverseFiniteOpen_isFinite` along `W ≅ W'`. -/
instance inverseAmbient_isFinite (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U) :
    IsFinite
      ((inverseAmbientOpen f ybar x U u).ι ≫
        baseChangeToBase f (inverseBaseEtale f ybar x U u)) :=
  sorry

/-- Finite-support pair on the twice-shrunk neighbourhood associated to a section
of `F` on an étale neighbourhood of `x̄`. The subscheme is the pulled-back `W'`,
isomorphic to the Lemma 37.41.3 finite open after the second shrinking. -/
def inverseSupportTerm (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U)
    (s : F.1.obj (op U)) :
    FiniteSupportTerm f F (inverseBaseEtale f ybar x U u) :=
  FiniteSupportTerm.of f F (inverseBaseEtale f ybar x U u)
    (inverseAmbientOpen f ybar x U u).toScheme
    (inverseAmbientOpen f ybar x U u).ι
    (inverseAmbientOpen f ybar x U u)
    sorry
    sorry
    ((F.1.map (inverseAmbientToU f ybar x U u).op).hom s)
    sorry

/-- The inverse finite-support pair is the pulled-back `W'`, finite over the
twice-shrunk base by base change of Lemma 37.41.3, and isomorphic to the
pulled-back finite open. -/
theorem inverseSupportTerm_spec (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (x : Over f ybar) (U : X.Etale)
    (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U)
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
def stalkToLowerShriekPresheafFiber
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Over f ybar) :
    (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F ⟶
      (toSmallEtalePoint ybar).presheafFiber.obj ((lowerShriekPresheaf f).obj F) :=
  (toSmallEtalePoint x.toGeometricPoint).presheafFiberDesc
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
theorem stalkToLowerShriekPresheafFiber_germ
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Over f ybar)
    (U : X.Etale) (u : (toSmallEtalePoint x.toGeometricPoint).fiber.obj U)
    (s : F.1.obj (op U)) :
    stalkToLowerShriekPresheafFiber f ybar F x
        ((toSmallEtalePoint x.toGeometricPoint).toPresheafFiber U u F.1 s) =
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
    Sigma.desc fun x : Over f ybar ↦
      stalkToLowerShriekPresheafFiber f ybar F x
  naturality := sorry

/-- Evaluating the inverse comparison at an abelian étale sheaf. -/
theorem lowerShriekPresheafStalkComparisonInv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekPresheafStalkComparisonInv f ybar).app F =
      Sigma.desc fun x : Over f ybar ↦
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

end AlgebraicGeometry.Scheme.Etale

end
