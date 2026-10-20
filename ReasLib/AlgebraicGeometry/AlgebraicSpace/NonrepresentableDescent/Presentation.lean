module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.FieldTheory.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Quadratic Galois étale equivalence relation

This module records the affine line `S = Spec(k[x])`, the cover `U = Spec(k'[x])` of a
degree-2 Galois extension, the unique nontrivial Galois graph, and the étale equivalence
relation `R = Δ(U) ⨿ Δ'(U \ {0_U})`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open Polynomial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- The index of the two relation summands: the diagonal copy of `U`, and the punctured
graph of the nontrivial Galois element. -/
abbrev relationIndex : Type := Bool

/-- The relation index is the two-element type of diagonal versus punctured-graph summands. -/
theorem relationIndex_eq : relationIndex = Bool := rfl

/-- The base scheme `S = Spec(k[x])`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k))

/-- The base scheme is the spectrum of `k[x]`. -/
theorem base_eq (k : Type u) [Field k] :
    base k = Spec (CommRingCat.of (Polynomial k)) := rfl

/-- The structure morphism of the cover, induced by `k[x] → k'[x]`. -/
def coverAlgebraMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    CommRingCat.of (Polynomial k) ⟶ CommRingCat.of (Polynomial k') :=
  CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))

/-- The structure map of the cover is `Polynomial.mapRingHom` of the algebra map. -/
theorem coverAlgebraMap_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    coverAlgebraMap k k' =
      CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k')) := rfl

/-- The scheme `U = Spec(k'[x])` over `S = Spec(k[x])`. -/
def cover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Over (base k) :=
  OverSpec.affine (coverAlgebraMap k k')

/-- The underlying scheme of the cover is `Spec(k'[x])`. -/
theorem cover_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (cover k k').left = Spec (CommRingCat.of (Polynomial k')) := rfl

/-- The structure morphism of the cover is `Spec` of `k[x] → k'[x]`. -/
theorem cover_hom_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (cover k k').hom = Spec.map (coverAlgebraMap k k') := rfl

/-- The morphism `U → S` is étale. -/
theorem etale_cover_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Etale (cover k k').hom := sorry

/-- The morphism `U → S` is finite. -/
theorem isFinite_cover_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    IsFinite (cover k k').hom := sorry

/-- The morphism `U → S` is surjective. -/
theorem surjective_cover_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Surjective (cover k k').hom := sorry

/-- The unique nontrivial element of `Gal(k'/k)` for a degree-2 Galois extension. -/
def galConj (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) : Gal(k'/k) :=
  (fun _ : Module.finrank k k' = 2 ↦ Classical.epsilon fun σ : Gal(k'/k) ↦ σ ≠ 1) hdeg

/-- The chosen Galois element is not the identity. -/
theorem galConj_ne_one (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galConj k k' hdeg ≠ 1 := sorry

/-- Every Galois element is the identity or `galConj`. -/
theorem eq_one_or_galConj (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (σ : Gal(k'/k)) :
    σ = 1 ∨ σ = galConj k k' hdeg := sorry

/-- Any nontrivial Galois element equals `galConj`. -/
theorem galConj_unique (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) {σ : Gal(k'/k)} (hσ : σ ≠ 1) :
    σ = galConj k k' hdeg := sorry

/-- The ring homomorphism of the Galois action on `k'[x]`. -/
def galActRingHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    CommRingCat.of (Polynomial k') ⟶ CommRingCat.of (Polynomial k') :=
  CommRingCat.ofHom (Polynomial.mapRingHom (galConj k k' hdeg).toRingHom)

/-- The Galois action on coordinate rings is `Polynomial.mapRingHom` of `galConj`. -/
theorem galActRingHom_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galActRingHom k k' hdeg =
      CommRingCat.ofHom (Polynomial.mapRingHom (galConj k k' hdeg).toRingHom) := rfl

/-- The scheme morphism of the Galois action on `U`. -/
def galActLeft (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (cover k k').left ⟶ (cover k k').left :=
  Spec.map (galActRingHom k k' hdeg)

/-- The underlying scheme morphism of the Galois action is `Spec` of `galActRingHom`. -/
theorem galActLeft_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galActLeft k k' hdeg = Spec.map (galActRingHom k k' hdeg) := rfl

/-- The Galois action on `U` lies over `S`. -/
theorem galAct_comp_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galActLeft k k' hdeg ≫ (cover k k').hom = (cover k k').hom := sorry

/-- The Galois action as a morphism of schemes over `S`. -/
def galAct (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    cover k k' ⟶ cover k k' :=
  Over.homMk (galActLeft k k' hdeg) (galAct_comp_hom k k' hdeg)

/-- The underlying scheme morphism of `galAct` is `galActLeft`. -/
theorem galAct_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (galAct k k' hdeg).left = galActLeft k k' hdeg := rfl

/-- The Galois action is étale. -/
instance instEtale_galAct (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Etale (galAct k k' hdeg).left := sorry

/-- The origin of `U`, as `Spec(k') → Spec(k'[x])` given by evaluation at `0`. -/
def originHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Spec (CommRingCat.of k') ⟶ (cover k k').left :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k')))

/-- The origin morphism is `Spec` of evaluation at `0`. -/
theorem originHom_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    originHom k k' =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k'))) := rfl

/-- The `k'`-rational origin `0_U ∈ |U|`. -/
def origin (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : (cover k k').left :=
  originHom k k' (IsLocalRing.closedPoint k')

/-- The origin point lies in the image of `originHom`. -/
theorem origin_mem_range (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    origin k k' ∈ Set.range (originHom k k') := ⟨IsLocalRing.closedPoint k', rfl⟩

/-- The global coordinate section `x` on `Spec(R[x])`. -/
def coordinateX (R : Type u) [CommRing R] : Γ(Spec (CommRingCat.of (Polynomial R)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv Polynomial.X

/-- The coordinate section is the image of `Polynomial.X` under `ΓSpecIso`. -/
theorem coordinateX_eq (R : Type u) [CommRing R] :
    coordinateX R =
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv Polynomial.X := rfl

/-- The punctured open `U \ {0_U} = D(x)`. -/
def puncturedOpen (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (cover k k').left.Opens :=
  (cover k k').left.basicOpen (coordinateX k')

/-- The punctured open is the basic open of the coordinate section. -/
theorem puncturedOpen_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    puncturedOpen k k' = (cover k k').left.basicOpen (coordinateX k') := rfl

/-- The open immersion of the punctured locus into `U`. -/
def puncturedι (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (puncturedOpen k k').toScheme ⟶ (cover k k').left :=
  (puncturedOpen k k').ι

/-- The punctured inclusion is the open-immersion structure map of `D(x)`. -/
theorem puncturedι_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    puncturedι k k' = (puncturedOpen k k').ι := rfl

/-- The punctured inclusion is an open immersion. -/
instance instIsOpenImmersion_puncturedι (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    IsOpenImmersion (puncturedι k k') := by
  change IsOpenImmersion (puncturedOpen k k').ι
  infer_instance

/-- The underlying set of the punctured open is the complement of the origin. -/
theorem coe_puncturedOpen (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (puncturedOpen k k' : Set (cover k k').left) = {origin k k'}ᶜ := sorry

/-- The punctured locus as a scheme over `S`. -/
def puncturedOver (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Over (base k) :=
  Over.mk (puncturedι k k' ≫ (cover k k').hom)

/-- The structure morphism of the punctured locus is the composite through `U → S`. -/
theorem puncturedOver_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (puncturedOver k k').hom = puncturedι k k' ≫ (cover k k').hom := rfl

/-- The open immersion `U \ {0_U} ⟶ U` as a morphism over `S`. -/
def puncturedιOver (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    puncturedOver k k' ⟶ cover k k' :=
  Over.homMk (puncturedι k k')

/-- The underlying scheme morphism of `puncturedιOver` is `puncturedι`. -/
theorem puncturedιOver_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (puncturedιOver k k').left = puncturedι k k' := rfl

/-- The relative diagonal `Δ : U ⟶ U ×_S U`. -/
def diagonalHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    cover k k' ⟶ cover k k' ⨯ cover k k' :=
  prod.lift (𝟙 (cover k k')) (𝟙 (cover k k'))

/-- The relative diagonal is the product lift of two identity morphisms. -/
theorem diagonalHom_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    diagonalHom k k' = prod.lift (𝟙 (cover k k')) (𝟙 (cover k k')) := rfl

/-- The graph `Δ' = (1, σ) : U ⟶ U ×_S U` of the nontrivial Galois action. -/
def graphHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    cover k k' ⟶ cover k k' ⨯ cover k k' :=
  prod.lift (𝟙 (cover k k')) (galAct k k' hdeg)

/-- The Galois graph is the product lift of the identity and `galAct`. -/
theorem graphHom_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    graphHom k k' hdeg = prod.lift (𝟙 (cover k k')) (galAct k k' hdeg) := rfl

/-- The coproduct of the two graphs is an isomorphism `U ⨿ U ≅ U ×_S U`. -/
theorem isIso_coprod_desc_diagonal_graph (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    IsIso (coprod.desc (diagonalHom k k') (graphHom k k' hdeg)) := sorry

/-- The `i`-th summand of the relation scheme: `U` on the diagonal, and `U \ {0_U}` on
the Galois graph. -/
def relationComponent (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    relationIndex → Over (base k)
  | false => cover k k'
  | true => puncturedOver k k'

/-- The diagonal summand of the relation is the cover `U`. -/
theorem relationComponent_false (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    relationComponent k k' false = cover k k' := rfl

/-- The off-diagonal summand of the relation is the punctured locus. -/
theorem relationComponent_true (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    relationComponent k k' true = puncturedOver k k' := rfl

/-- The component of `j` on each summand: the relative diagonal on `U`, and the restricted
Galois graph on `U \ {0_U}`. -/
def relationComponentHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (i : relationIndex) → relationComponent k k' i ⟶ cover k k' ⨯ cover k k'
  | false => diagonalHom k k'
  | true => puncturedιOver k k' ≫ graphHom k k' hdeg

/-- On the diagonal summand, `j` is the relative diagonal of `U` over `S`. -/
theorem relationComponentHom_false (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    relationComponentHom k k' hdeg false = diagonalHom k k' := rfl

/-- On the punctured summand, `j` is the Galois graph restricted along `D(x)`. -/
theorem relationComponentHom_true (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    relationComponentHom k k' hdeg true = puncturedιOver k k' ≫ graphHom k k' hdeg := rfl

/-- The relation scheme `R = Δ(U) ⨿ Δ'(U \ {0_U})` as an object over `S`. -/
def relationOver (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Over (base k) :=
  ∐ (relationComponent k k')

/-- The underlying object of `relationOver` is the coproduct of the two summands. -/
theorem relationOver_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    relationOver k k' = ∐ (relationComponent k k') := rfl

/-- The morphism `j : R ⟶ U ×_S U` equal to `Δ` on `U` and to `Δ'` on `U \ {0_U}`. -/
def relationHom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    relationOver k k' ⟶ cover k k' ⨯ cover k k' :=
  Sigma.desc (relationComponentHom k k' hdeg)

/-- The defining map of the relation is the coproduct fold of the component maps. -/
theorem relationHom_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    relationHom k k' hdeg = Sigma.desc (relationComponentHom k k' hdeg) := rfl

/-- The pre-relation on `U` over `S` with source `R` and defining map `j`. -/
def preRelation (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) : Scheme.PreRelation (cover k k') :=
  Scheme.PreRelation.ofHom (relationHom k k' hdeg)

/-- The defining arrow of `preRelation` is `relationHom`. -/
theorem preRelation_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (preRelation k k' hdeg).hom = relationHom k k' hdeg := rfl

/-- The first projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_t_false (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sigma.ι (relationComponent k k') false ≫ (preRelation k k' hdeg).t = 𝟙 (cover k k') :=
  sorry

/-- The second projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_s_false (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sigma.ι (relationComponent k k') false ≫ (preRelation k k' hdeg).s = 𝟙 (cover k k') :=
  sorry

/-- The first projection of the relation, restricted to the punctured summand, is the
punctured inclusion. -/
theorem preRelation_t_true (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sigma.ι (relationComponent k k') true ≫ (preRelation k k' hdeg).t =
      puncturedιOver k k' := sorry

/-- The second projection of the relation, restricted to the punctured summand, is the
punctured inclusion followed by the Galois action. -/
theorem preRelation_s_true (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sigma.ι (relationComponent k k') true ≫ (preRelation k k' hdeg).s =
      puncturedιOver k k' ≫ galAct k k' hdeg := sorry

/-- The two projections of `j` are étale and `j` is an equivalence relation. -/
instance instIsEtaleEquivalenceRelation_preRelation (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    (preRelation k k' hdeg).IsEtaleEquivalenceRelation := sorry

/-- The origin of `S`, as `Spec(k) → Spec(k[x])` given by evaluation at `0`. -/
def originBase (k : Type u) [Field k] : Spec (CommRingCat.of k) ⟶ base k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))

/-- The origin of `S` is `Spec` of evaluation at `0`. -/
theorem originBase_eq (k : Type u) [Field k] :
    originBase k = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := rfl

/-- The punctured open `S \ {0_S} = D(x)`. -/
def basePuncturedOpen (k : Type u) [Field k] : (base k).Opens :=
  (base k).basicOpen (coordinateX k)

/-- The punctured base is the basic open of the coordinate section on `S`. -/
theorem basePuncturedOpen_eq (k : Type u) [Field k] :
    basePuncturedOpen k = (base k).basicOpen (coordinateX k) := rfl

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
